/// Shared helpers for the `tao` CLI commands: expanding CLI paths to
/// `.tao` files, loading modules with the prelude, compiling them, and
/// printing errors.
import core/context.{type Context, Context, new_ctx}
import core/error.{type Error}
import core/ffi
import core/format
import core/value.{type Value}
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{None}
import gleam/string
import simplifile
import tao/ast.{type Module}
import tao/compile
import tao/load
import utils/fs

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil

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
/// prelude package (loaded from `lib/prelude`).
pub fn load(paths: List(String)) -> Result(Loaded, String) {
  case expand_paths(paths) {
    Error(msg) -> Error(msg)
    Ok(files) -> {
      let #(mods, errors) = load_modules(files)
      let #(prelude, prelude_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      Ok(Loaded(
        paths: files,
        mods: mods,
        prelude: prelude,
        errors: list.append(errors, prelude_errors),
      ))
    }
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
/// do).
pub fn compile(mods: List(Module), prelude: List(Module)) -> Context {
  let all = list.append(mods, prelude)
  let all = load.implicit_prelude_imports(all, prelude)
  compile.modules(Context(..new_ctx, ffi: ffi.build), all)
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
