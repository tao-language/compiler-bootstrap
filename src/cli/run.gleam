/// `tao run <file>` — load the file (and the prelude), type-check it,
/// then evaluate the file's top-level definitions and print their
/// values to stdout. Prints errors to stderr and exits with status 1
/// when there are errors, 0 otherwise.
import cli/common
import core/context
import core/value as v
import gleam/io
import gleam/list
import gleam/option.{Some}
import tao/ast.{type Module} as tao

pub fn run(files: List(String)) -> Nil {
  case files {
    [file] -> run_file(file)
    _ -> {
      io.println_error("error: run takes exactly one file")
      common.exit(1)
    }
  }
}

fn run_file(file: String) -> Nil {
  case common.load([file]) {
    Error(msg) -> {
      io.println_error("error: " <> msg)
      common.exit(1)
    }
    Ok(loaded) ->
      case list.length(loaded.errors) {
        0 -> {
          let ctx = common.compile(loaded.mods, loaded.prelude)
          common.print_build_errors(ctx)
          case ctx.errors {
            [] -> print_values(ctx, loaded.mods)
            _ -> common.exit(1)
          }
        }
        _ -> {
          common.print_syntax_errors(loaded.errors)
          common.exit(1)
        }
      }
  }
}

/// Print the value of every top-level `let` binding in the file (the
/// definitions live in the module's record).
fn print_values(ctx: context.Context, mods: List(Module)) -> Nil {
  case mods {
    [#(mod_name, stmts), ..] -> {
      case context.lookup_var(ctx, mod_name) {
        Some(#(v.Rcd(values, _), _)) -> {
          list.map(stmts, fn(stmt) {
            case stmt.data {
              tao.LetVar(name, _, _) ->
                case list.key_find(values, name) {
                  Ok(#(value, _)) ->
                    io.println(name <> " = " <> common.fmt_value(ctx, value))
                  Error(Nil) -> Nil
                }
              _ -> Nil
            }
          })
          Nil
        }
        _ -> Nil
      }
    }
    [] -> Nil
  }
}
