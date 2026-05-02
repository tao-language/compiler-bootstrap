/// Compiler Bootstrap CLI — entry point
///
/// Usage:
///   gleam run -- module compiler_bootstrap run <file.core>
///   gleam run -- module compiler_bootstrap run -c 'expression'
///   gleam run -- module compiler_bootstrap run --help
///   gleam run -- module compiler_bootstrap check <file.core>

import cli/run as cli
import gleam/io
import argv

pub fn main() {
  let args = command_line_args()

  case cli.parse_args(args) {
    Ok(command) -> cli.run_command(command)
    Error(msg) -> {
      io.println("Error: " <> msg)
      cli.show_help()
    }
  }
}

/// Get command line arguments, skipping the program name.
fn command_line_args() -> List(String) {
  let argv.Argv(arguments: args, ..) = argv.load()
  args
}
