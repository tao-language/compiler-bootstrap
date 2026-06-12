/// Debug Core CLI Command — Inspect the full compiler pipeline
import core/ast
import core/context.{new_ctx}
import core/eval.{eval}
import core/format.{format}
import core/infer.{infer}
import core/parse.{parse}
import core/quote.{quote}
import core/resolve.{resolve}
import core/term
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import syntax/span

/// This command takes a Core expression string and runs the entire
/// pipeline, printing structured debug information at each stage.
pub fn debug_core(source: String, width: Int) -> Nil {
  io.println(">> source")
  io.println(source)
  io.println("")

  io.println(">> parse(source) -> AST")
  let ast = case parse("<cli>", source) {
    Ok(ast) -> ast
    Error(err) -> {
      io.print_error(string.inspect(err))
      ast.err(span.Span("<syntax error>", 0, 0, 0, 0))
    }
  }
  io.println(format(ast, width))
  io.println("")

  io.println(">> infer(ast) -> (Term, Type)")
  let #(term, type_, ctx) = infer(new_ctx, ast)
  case list.length(ctx.errors) {
    0 -> Nil
    num_errors -> {
      io.println("// Errors (" <> int.to_string(num_errors) <> ")")
      list.map(ctx.errors, fn(err) { io.println("- " <> string.inspect(err)) })
      io.println("")
    }
  }

  case list.length(ctx.subst) {
    0 -> Nil
    num_subst -> {
      io.println("// Subst (" <> int.to_string(num_subst) <> ")")
      list.map(ctx.subst, fn(subst) {
        io.println("- " <> string.inspect(subst))
      })
      io.println("")
    }
  }

  io.println("// Type")
  let type_term = quote(ctx.ffi, 0, type_)
  let type_ast = term.to_ast(type_term, [])
  io.println(format(type_ast, width))
  io.println("")

  io.println("// Term (raw)")
  let term_ast = term.to_ast(term, [])
  io.println(format(term_ast, width))
  io.println("")

  io.println("// Term (holes resolved)")
  let term = resolve(ctx.ffi, ctx.subst, 0, term)
  let term_ast = term.to_ast(term, [])
  io.println(format(term_ast, width))
  io.println("")

  io.println(">> eval(term) -> Value")
  let result_val = eval(ctx.ffi, [], term)
  let result_term = quote(ctx.ffi, 0, result_val)
  let result_ast = term.to_ast(result_term, [])
  io.println(format(result_ast, width))
  io.println("")
}
