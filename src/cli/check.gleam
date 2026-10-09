/// `tao check [paths..]` — load the given `.tao` files (and the
/// prelude), type-check them, and print any errors to stderr. Exits
/// with status 1 when there are errors, 0 otherwise.
import cli/common
import core/context.{type TraceKind}
import gleam/io
import gleam/list

pub fn check(paths: List(String), trace_kinds: List(TraceKind)) -> Nil {
  case common.load(paths) {
    Error(msg) -> {
      io.println_error("error: " <> msg)
      common.exit(1)
    }
    Ok(loaded) ->
      case list.length(loaded.errors) {
        0 -> {
          let ctx = common.compile(loaded.mods, trace_kinds)
          common.print_build_errors(ctx)
          case ctx.errors {
            [] -> Nil
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
