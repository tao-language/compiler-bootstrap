import cli/args.{InputExpr, InputFiles, InputStmts, parse}
import cli/check.{check}
import cli/debug_core.{debug_core}
import cli/run.{run}
import cli/run_tests.{run_tests}
import gleam/io

const help = "Tao compiler bootstrap\n\nUsage:\n  tao check [paths...]                   Type-check .tao files (default: .)\n  tao run <file>                         Compile and run a .tao file\n  tao test [paths...]                    Run tests in .tao files (default: .)\n      -e <expr>, --expr <expr>           Compile a single expression\n      -s <stmts>, --stmt <stmts>         Compile statements as an anonymous\n                                         module (newline or ; separated)\n      --trace <kind>                     Enable a compiler trace (repeatable):\n                                         parse, modules, defines, holes,\n                                         solves, desugar, infer, resolve,\n                                         eval, tests\n      --dump-def <name>                  Print <name>'s inferred type with de\n                                         Bruijn indices, then stop\n      --path <dir>                       Extra package path (repeatable,\n                                         default: lib)\n      --add <name[:version]>             Extra package to load (repeatable)\n  tao test additionally accepts:\n      --filter <pattern>                 Only run matching tests (repeatable)\n      --skip <pattern>                   Skip matching tests (repeatable)\n      <path>:<test1,test2>               Restrict the tests run in a file\n  tao debug-core 'core-term'             Debug a Core term\n  tao --help                             Show this help\n\ncheck and test accept file and directory paths; directories are searched\nrecursively for .tao files. If no paths are given, the current directory\nis used. -e and -s take the source directly instead of a file and go\nthrough the same parser and pipeline. test's --filter/--skip patterns\nmatch a test name or a module path with a test name (module/path.tao:test_name),\nwith * and ** glob wildcards.\n"

/// The CLI entry point. Commands: `check`, `run`, `test`, `debug-core`,
/// `--help`. The REPL is TODO.
pub fn entrypoint(args: List(String)) {
  case args {
    [] -> {
      io.println(help)
      exit(0)
    }
    ["--help", ..] -> {
      io.println(help)
      exit(0)
    }
    ["check", ..args] ->
      case parse("check", args) {
        Error(msg) -> usage_error(msg)
        Ok(opts) -> check(opts)
      }
    ["run", ..args] ->
      case parse("run", args) {
        Error(msg) -> usage_error(msg)
        Ok(opts) -> case opts.input {
          InputFiles([_]) -> run(opts)
          InputExpr(..) | InputStmts(..) -> run(opts)
          InputFiles(_) -> usage_error("run takes exactly one file")
        }
      }
    ["test", ..args] ->
      case parse("test", args) {
        Error(msg) -> usage_error(msg)
        Ok(opts) -> run_tests(opts)
      }
    ["debug-core", source, ..] -> debug_core(source, 80)
    _ -> {
      io.println_error("error: unknown command")
      io.println(help)
      exit(1)
    }
  }
}

fn usage_error(msg: String) -> Nil {
  io.println_error("error: " <> msg)
  io.println(help)
  exit(1)
}

/// Terminate the process with `status`.
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
