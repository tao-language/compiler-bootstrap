/// Shared helpers for the `tao` CLI commands: expanding CLI paths to
/// `.tao` files, printing errors, and formatting values. The compile
/// pipeline itself lives in `cli/pipeline`.
import core/context.{type Context}
import core/error.{type Error}
import core/format
import core/value.{type Value}
import filepath
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import simplifile
import utils/fs

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil

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

/// Print a loading error (`error: …`) to stderr and exit 1.
pub fn load_failure(msg: String) -> Nil {
  io.println_error("error: " <> msg)
  exit(1)
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
