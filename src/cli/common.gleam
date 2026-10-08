/// Shared helpers for the `tao` CLI commands: expanding CLI paths to
/// `.tao` files, loading modules with the prelude, compiling them, and
/// printing errors.
import core/context.{type Context, type TraceKind, Context, new_ctx}
import core/error.{type Error}
import core/ffi
import core/format
import core/value.{type Value}
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import simplifile
import tao/ast.{type Module}
import tao/compile
import tao/load
import utils/fs

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil

/// The package list with the prelude (the standard library) added, so
/// every command compiles against it (skipped when already present).
pub fn with_prelude(
  packages: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case list.any(packages, fn(p) { p.0 == "prelude" }) {
    True -> packages
    False -> list.append(packages, [#("prelude", None)])
  }
}

/// Modules loaded from the given paths, plus the prelude (the standard
/// library) and any syntax errors encountered while loading.
pub type Loaded {
  Loaded(
    /// The expanded `.tao` file paths, in order.
    paths: List(String),
    /// The loaded modules, one per path, in the same order.
    mods: List(Module),
    /// The prelude modules.
    prelude: List(Module),
    /// Syntax (read/parse) errors, if any.
    errors: List(Error),
  )
}

/// Expand CLI paths to `.tao` file paths: file paths are passed through
/// and directory paths are traversed recursively. An empty list is
/// treated as `["."]` (all `.tao` files in the current directory,
/// recursively).
pub fn expand_paths(paths: List(String)) -> Result(List(String), String) {
  let paths = case paths {
    [] -> ["."]
    _ -> paths
  }
  expand(paths, [])
}

fn expand(
  paths: List(String),
  acc: List(String),
) -> Result(List(String), String) {
  case paths {
    [] -> Ok(list.unique(acc))
    [path, ..rest] ->
      case expand_path(path) {
        Error(msg) -> Error(msg)
        Ok(files) -> expand(rest, list.append(acc, files))
      }
  }
}

fn expand_path(path: String) -> Result(List(String), String) {
  case simplifile.is_file(path) {
    Ok(True) -> Ok([normalize(path)])
    _ ->
      case fs.is_directory(path) {
        Ok(True) ->
          case
            fs.list_recursive(path, fn(file) { string.ends_with(file, ".tao") })
          {
            Ok(files) ->
              Ok(
                list.map(files, fn(file) {
                  normalize(filepath.join(path, file))
                }),
              )
            Error(msg) -> Error(msg)
          }
        _ -> Error("no such file or directory: " <> path)
      }
  }
}

/// Strip a leading `./` from a path (e.g. `filepath.join(".", "a")` is
/// `"./a"`).
pub fn normalize(path: String) -> String {
  case path {
    "./" <> rest -> rest
    _ -> path
  }
}

/// Expand `paths` and load every `.tao` file in it, along with the
/// prelude package (loaded from `lib/prelude`). Input files that are
/// themselves part of the prelude package are replaced by their package
/// copy (the same file loaded under the package's module name), so the
/// file is never compiled twice under two names.
pub fn load(paths: List(String)) -> Result(Loaded, String) {
  case expand_paths(paths) {
    Error(msg) -> Error(msg)
    Ok(files) -> {
      let #(mods, errors) = load_modules(files)
      let #(prelude, prelude_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      Ok(Loaded(
        paths: files,
        mods: prelude_copies(mods, prelude),
        prelude: prelude,
        errors: list.append(errors, prelude_errors),
      ))
    }
  }
}

/// Replace modules loaded from the prelude package directory by the
/// package's own copy of the same file (matched by the path after the
/// version directory), keeping the other modules unchanged.
fn prelude_copies(
  mods: List(Module),
  prelude: List(Module),
) -> List(Module) {
  list.map(mods, fn(mod) {
    case prelude_package_name(mod.0) {
      Some(pkg_name) ->
        // Prelude module names are unique, so the first (only) match wins.
        case list.find(prelude, fn(m) { m.0 == pkg_name }) {
          Ok(pkg_mod) -> pkg_mod
          Error(Nil) -> mod
        }
      None -> mod
    }
  })
}

/// The prelude package name of a module loaded from the prelude package
/// directory (e.g. `/lib/prelude/v0.0.1/result` → `/prelude/result`), if
/// any.
fn prelude_package_name(name: String) -> Option(String) {
  case name {
    "/lib/prelude/" <> rest ->
      case string.split(rest, "/") {
        [_version, ..parts] -> Some("/prelude/" <> string.join(parts, "/"))
        _ -> None
      }
    _ -> None
  }
}

fn load_modules(files: List(String)) -> #(List(Module), List(Error)) {
  case files {
    [] -> #([], [])
    [file, ..files] -> {
      let #(stmts, errors) = load.file(file)
      // Module names are the file path without extension, prefixed with
      // `/` (module names always start with `/`).
      let name = "/" <> filepath.strip_extension(file)
      let #(mods, rest) = load_modules(files)
      #([#(name, stmts), ..mods], list.append(errors, rest))
    }
  }
}

/// Type-check `mods` together with the prelude, making the prelude names
/// available in every module (as the `debug-file` CLI and the corpus test
/// do). Modules that duplicate a prelude package module are dropped:
/// loading the same file twice under two names creates duplicate module
/// records (the path copy would also get implicit prelude imports of
/// itself).
pub fn compile(
  mods: List(Module),
  prelude: List(Module),
  trace_kinds: List(TraceKind),
) -> Context {
  let prelude_names = list.map(prelude, fn(mod) { mod.0 })
  let mods = list.filter(mods, fn(mod) {
    !list.contains(prelude_names, mod.0)
  })
  let all = list.append(mods, prelude)
  let all = load.implicit_prelude_imports(all, prelude)
  compile.modules(
    Context(..new_ctx, ffi: ffi.build, trace_kinds: trace_kinds),
    all,
  )
}

/// Print syntax (read/parse) errors to stderr.
pub fn print_syntax_errors(errors: List(Error)) -> Nil {
  case errors {
    [] -> Nil
    errors -> {
      let n = list.length(errors)
      io.println_error("---- SYNTAX ERRORS ----")
      list.map(errors, fn(err) {
        io.println_error("❌ " <> error.display_syntax(err))
      })
      io.println_error("")
      io.println_error(int.to_string(n) <> " syntax errors")
    }
  }
}

/// Print the build (type-checking) errors of a context to stderr.
pub fn print_build_errors(ctx: Context) -> Nil {
  case ctx.errors {
    [] -> Nil
    errors -> {
      let n = list.length(errors)
      io.println_error("---- BUILD ERRORS ----")
      list.map(errors, fn(err) {
        io.println_error("❌ " <> error.display(ctx.ffi, ctx.types, err))
      })
      io.println_error("")
      io.println_error(int.to_string(n) <> " build errors")
    }
  }
}

/// Format a value for display.
pub fn fmt_value(ctx: Context, value: Value) -> String {
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  format.value(ctx.ffi, names, value, 80, 2)
}
