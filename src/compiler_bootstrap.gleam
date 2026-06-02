/// Compiler Bootstrap CLI — entry point
///
/// Usage:
///   gleam run <file.core>
///   gleam run -c 'expression'
///   gleam run --help
///   gleam run check <file.core>
import argv.{Argv}
import cli/debug_core
import cli/run as cli
import gleam/io

const help = "Tao compiler bootstrap

Usage:
  tao <filename>                Run a .tao or .core file
  tao -c 'expression'           Run a Tao expression
  tao debug-core 'expression'   Debug a Core expression
  tao --help                    Show this help
"

pub fn main() {
  let Argv(arguments: args, ..) = argv.load()
  todo
  // case parse_args(args) {
  //   Ok(command) -> run_command(command)
  //   Error(msg) -> {
  //     io.println("Error: " <> msg)
  //     io.print(help)
  //   }
  // }
}
// /// Parse command-line arguments into a Command.
// pub fn parse_args(args: List(String)) -> Result(Command, String) {
//   case args {
//     ["--help", ..] -> Ok(Help)
//     ["--debug", path, ..rest] ->
//       case rest {
//         [] -> Ok(Run(File(path), False, True))
//         _ -> Error("Too many arguments for --debug")
//       }
//     ["-c", expr, ..rest] ->
//       case rest {
//         [] -> Ok(Run(Inline(expr), False, False))
//         _ -> Error("Too many arguments after -c expression")
//       }
//     ["debug-core", expr, ..rest] ->
//       case parse_debug_flags(rest, False, False) {
//         Ok(flags) -> Ok(DebugCore(expr, flags.0, flags.1))
//         Error(msg) -> Error(msg)
//       }
//     [path, ..rest] ->
//       case rest {
//         [] -> Ok(Run(File(path), False, False))
//         _ -> Error("Too many arguments")
//       }
//     _ -> Ok(Help)
//   }
// }

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
