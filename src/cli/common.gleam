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
import gleam/option.{type Option, None}
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
    /// All loaded modules (including prelude), with canonical names.
    mods: List(Module),
    /// The names of the prelude modules (for implicit imports).
    prelude_names: List(String),
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
/// prelude package. Files that are inside the prelude package directory
/// are named by their canonical package path (e.g. `/prelude/bool`),
/// deduplicated against the package modules.
pub fn load(paths: List(String)) -> Result(Loaded, String) {
  case expand_paths(paths) {
    Error(msg) -> Error(msg)
    Ok(files) -> {
      let packages = with_prelude([])
      let #(mods, errors) = load.project(["lib"], files, packages)
      let prelude_names =
        list.filter_map(mods, fn(m) {
          case m.0 {
            "/prelude" -> Ok(m.0)
            "/prelude/" <> _ -> Ok(m.0)
            _ -> Error(Nil)
          }
        })
      Ok(Loaded(
        paths: files,
        mods: mods,
        prelude_names: prelude_names,
        errors: errors,
      ))
    }
  }
}

/// Type-check `mods`, making the prelude names available in every
/// module via implicit imports.
pub fn compile(
  mods: List(Module),
  prelude_names: List(String),
  trace_kinds: List(TraceKind),
) -> Context {
  let prelude = list.filter(mods, fn(m) { list.contains(prelude_names, m.0) })
  let all = load.implicit_prelude_imports(mods, prelude)
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
