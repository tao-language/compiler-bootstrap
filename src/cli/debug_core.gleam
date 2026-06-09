/// Debug Core CLI Command — Inspect the full compiler pipeline
import gleam/io

/// This command takes a Core expression string and runs the entire
/// pipeline, printing structured debug information at each stage.
pub fn debug_core(source: String) -> Nil {
  io.println("// source")
  io.println(source)
  io.println("")

  io.println("// parse(source) -> AST")
  todo as "TODO: parse"
  io.println("")
}
