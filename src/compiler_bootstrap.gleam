import argv.{Argv}
import cli/entrypoint.{entrypoint}

/// Compiler Bootstrap CLI — entry point
/// The CLI entry point. Commands: `check`, `run`, `test`, `debug-core`,
/// `--help`. The REPL is TODO.
pub fn main() -> Nil {
  let Argv(arguments: args, ..) = argv.load()
  entrypoint(args)
}
