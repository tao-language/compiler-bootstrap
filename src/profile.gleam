/// Profile entry point — wraps the gleeunit test runner in gflambe.
///
/// Run with:
///   gleam run --module profile -- [cli-args..] &> /dev/null
/// 
/// This generates file in the Brendan Gregg flame graph format.
/// The output file is created in `profiler/*-eflambe-output.bggg`
/// 
/// The output files are huge, typically >1GB.
import argv.{Argv}
import cli/entrypoint.{entrypoint}
import gflambe
import simplifile

const output_dir = "./profiler"

pub fn main() {
  // The output directory must exist.
  let _ = simplifile.create_directory(output_dir)
  let Argv(arguments: args, ..) = argv.load()

  // Run the full compiler CLI pipeline.
  gflambe.apply(fn() { entrypoint(args) }, [
    gflambe.OutputDirectory(output_dir),
    gflambe.OutputFormat(gflambe.BrendanGregg),
  ])
}
