/// Debug Core CLI Command — Inspect the full compiler pipeline
import core/ast
import core/context.{new_ctx}
import core/eval.{eval}
import core/format
import core/infer.{infer}
import core/parse.{parse}
import core/quote.{quote}
import core/resolve
import core/term
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import syntax/span.{Span}

/// This command takes a Core expression string and runs the entire
/// pipeline, printing structured debug information at each stage.
pub fn debug_core(source: String, width: Int) {
  io.println(">> source")
  io.println(source)
  io.println("")

  io.println(">> parse(source) -> AST")
  let expr = case parse("<cli>", source) {
    Ok(expr) -> expr
    Error(err) -> {
      io.print_error(string.inspect(err))
      ast.err(Span("<syntax error>", 0, 0, 0, 0))
    }
  }
  io.println(format.expr(expr, width, 2))
  io.println("")

  io.println(">> infer(ast) -> (Term, Type)")
  let #(term, type_, ctx) = infer(new_ctx, expr)
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
  let names = list.map(ctx.types, fn(t) { t.0 })
  io.println(format.value(ctx.ffi, names, type_, width, 2))
  io.println("")

  io.println("// Term (raw)")
  let term_ast = term.to_ast(term, [])
  io.println(format.expr(term_ast, width, 2))
  io.println("")

  io.println("// Term (holes resolved)")
  let term = resolve.term(ctx.ffi, ctx.subst, 0, term)
  let term_ast = term.to_ast(term, [])
  io.println(format.expr(term_ast, width, 2))
  io.println("")

  io.println(">> eval(term) -> Value")
  let result_val = eval(ctx.ffi, [], term)
  let result_term = quote(ctx.ffi, 0, result_val)
  let result_ast = term.to_ast(result_term, [])
  io.println(format.expr(result_ast, width, 2))
  io.println("")
}
