/// `tao run <file> | -e EXPR | -s STMTS` — compile the input, then
/// evaluate its top-level definitions and print their values to stdout
/// (an `-e` expression prints its value bare, REPL-style). Prints
/// errors to stderr and exits with status 1 when there are errors, 0
/// otherwise.
import cli/args.{type Opts, InputExpr}
import cli/common
import cli/pipeline
import core/context.{type Context}
import core/value as v
import gleam/io
import gleam/list
import gleam/option.{Some}
import tao/ast.{type Module} as tao

pub fn run(opts: Opts) -> Nil {
  case pipeline.compile_input(opts.input, opts) {
    Error(pipeline.LoadFailure(msg)) -> common.load_failure(msg)
    Error(pipeline.SyntaxFailures(errors)) -> {
      common.print_syntax_errors(errors)
      common.exit(1)
    }
    Ok(compiled) -> {
      common.print_build_errors(compiled.ctx)
      case compiled.ctx.errors {
        [] ->
          case opts.input {
            InputExpr(..) -> print_expr_value(compiled.ctx, compiled.modules)
            _ -> print_values(compiled.ctx, compiled.modules)
          }
        _ -> common.exit(1)
      }
    }
  }
}

/// `run -e`: print the wrapped expression's value bare (REPL-style).
fn print_expr_value(ctx: Context, mods: List(Module)) -> Nil {
  case mods {
    [#(mod_name, _), ..] ->
      case context.lookup_var(ctx, mod_name) {
        Some(#(v.Rcd(values, _), _)) ->
          case list.key_find(values, pipeline.expr_result_name) {
            Ok(#(value, _)) -> io.println(common.fmt_value(ctx, value))
            Error(Nil) -> Nil
          }
        _ -> Nil
      }
    [] -> Nil
  }
}

/// Print the value of every top-level `let` binding in the input
/// modules (the definitions live in the module's record).
fn print_values(ctx: Context, mods: List(Module)) -> Nil {
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
