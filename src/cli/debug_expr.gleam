import gleam/io

pub fn debug_expr(source: String, width: Int) {
  io.println(">> source")
  io.println(source)
  io.println("")

  io.println(">> parse(source) -> Expr")
  // let ast = case parse("<cli>", source) {
  //   Ok(ast) -> ast
  //   Error(err) -> {
  //     io.print_error(string.inspect(err))
  //     tao.err(Span("<syntax error>", 0, 0, 0, 0))
  //   }
  // }
  // io.println(string.inspect(ast))
  // io.println("")
  todo
}
