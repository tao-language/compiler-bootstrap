/// Compiler Bootstrap CLI — entry point
import argv.{Argv}
import cli/debug_core.{debug_core}
import cli/debug_expr.{debug_expr}
import cli/debug_file.{debug_file}
import cli/test_.{test_}
import gleam/io
import gleam/list
import gleam/option
import gleam/result
import gleam/string
import tao/config
import utils/glob.{glob_compile}

const help = "Tao compiler bootstrap

Usage:
  tao                                   Enter interactive REPL mode
  tao <filename>                        Run a .tao or .core file
  tao -c 'expression'                   Run a Tao expression
  tao test [..path] [--name='pattern']  Run tests
  tao debug-expr 'expression'           Debug a Tao expression
  tao debug-file <filename>             Debug a Tao module
  tao debug-core 'core-term'            Debug a Core term
  tao --help                            Show this help
"

pub fn main() {
  let Argv(arguments: args, ..) = argv.load()
  case args {
    [] -> todo as "TODO: CLI repl"
    ["--help", ..] -> {
      io.println(help)
      exit(0)
    }
    ["test", ..args] -> {
      // TODO: parse argument flags:
      // --name for test name patterns
      // --root for root directory
      let root =
        list.find_map(args, fn(arg) {
          case arg {
            "--root=" <> root -> Ok(root)
            _ -> Error(Nil)
          }
        })
        |> option.from_result
        |> option.or(config.find_project_root("."))
        |> option.unwrap(".")
      let paths = list.filter(args, fn(arg) { !string.starts_with(arg, "--") })
      let patterns =
        list.filter_map(args, fn(arg) {
          case arg {
            "--name=" <> pattern -> Ok(pattern)
            _ -> Error(Nil)
          }
        })
      let summary = test_(root, paths, patterns)
      let num_errors =
        list.length(summary.errors) + summary.num_fail + summary.num_neutral
      case num_errors > 0 {
        True -> exit(1)
        False -> Nil
      }
    }
    // ["-c", expr, ..rest] ->
    //   case rest {
    //     [] -> Ok(Run(Inline(expr), False, False))
    //     _ -> Error("Too many arguments after -c expression")
    //   }
    ["debug-expr", source, ..] -> debug_expr(source, 80)
    ["debug-file", ..args] -> {
      let root =
        list.find_map(args, fn(arg) {
          case arg {
            "--root=" <> root -> Ok(root)
            _ -> Error(Nil)
          }
        })
        |> option.from_result
        |> option.or(config.find_project_root("."))
        |> option.unwrap(".")
      let filename_result =
        list.filter(args, fn(arg) { !string.starts_with(arg, "--") })
        |> list.first
      case filename_result {
        Ok(filename) -> debug_file(root, filename, 80)
        Error(Nil) -> {
          io.println_error("error: no filename provided")
          io.println(help)
          exit(1)
        }
      }
    }
    ["debug-core", source, ..] -> debug_core(source, 80)
    // [path, ..rest] ->
    //   case rest {
    //     [] -> Ok(Run(File(path), False, False))
    //     _ -> Error("Too many arguments")
    //   }
    _ -> {
      echo args
      todo as "CLI command not implemented"
    }
  }
}

// /// Execute a command.
// pub fn run_command(command: Command) -> Nil {
//   case command {
//     Help -> {
//       show_help()
//       cli_halt(0)
//     }
//     Run(source, _, _) -> run_source(source)
//     Check(source, _, _) -> check_source(source)
//     DebugCore(expr, trace_parser, trace_infer) ->
//       debug_core.run(expr, trace_parser, trace_infer)
//   }
// }

// Declare the external Erlang halt function
@external(erlang, "erlang", "halt")
pub fn exit(status: Int) -> Nil
