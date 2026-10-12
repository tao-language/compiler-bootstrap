/// `tao check [paths...] | -e EXPR | -s STMTS` — compile the input
/// (files, an expression, or statements) and print any errors to
/// stderr. Exits with status 1 when there are errors, 0 otherwise.
import cli/args.{type Opts}
import cli/common
import cli/pipeline

pub fn check(opts: Opts) -> Nil {
  case pipeline.compile_input(opts.input, opts) {
    Error(pipeline.LoadFailure(msg)) -> common.load_failure(msg)
    Error(pipeline.SyntaxFailures(errors)) -> {
      common.print_syntax_errors(errors)
      common.exit(1)
    }
    Ok(compiled) -> common.print_build_errors(compiled.ctx)
  }
}
