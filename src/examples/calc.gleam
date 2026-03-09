// ============================================================================
// CALCULATOR EXAMPLE - Using Unified Grammar System
// ============================================================================
import gleam/int
import gleam/result
import syntax/formatter.{type Doc}
import syntax/grammar.{
  type Grammar, type Value, AstValue, ParensValue, TokenValue,
}

pub type Expr {
  Int(Int)
  Add(Expr, Expr)
  Sub(Expr, Expr)
  Mul(Expr, Expr)
  Div(Expr, Expr)
}

pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.left_assoc(
    "Expr",
    "Term",
    [
      grammar.op("+", Add, 10, " + "),
      grammar.op("-", Sub, 10, " - "),
    ],
    10,
  )
  |> grammar.left_assoc(
    "Term",
    "Factor",
    [
      grammar.op("*", Mul, 20, " * "),
      grammar.op("/", Div, 20, " / "),
    ],
    20,
  )
  |> grammar.rule("Factor", [
    grammar.alt(grammar.token_pattern("Number"), fn(values) {
      case values {
        [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
        _ -> panic as "Expected Number"
      }
    }),
    grammar.alt(grammar.parenthesized("Expr"), fn(values) {
      case values {
        [ParensValue([AstValue(expr)])] -> expr
        _ -> panic as "Expected parenthesized expr"
      }
    }),
  ])
}

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, -1) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  let grammar = calc_grammar()
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    // Use generic formatter helper with grammar metadata
    // Operator keys are the operator keywords ("+", "-", "*", "/")
    Add(l, r) ->
      grammar.format_binary_op(grammar, "+", l, r, parent_prec, format_expr)
    Sub(l, r) ->
      grammar.format_binary_op(grammar, "-", l, r, parent_prec, format_expr)
    Mul(l, r) ->
      grammar.format_binary_op(grammar, "*", l, r, parent_prec, format_expr)
    Div(l, r) ->
      grammar.format_binary_op(grammar, "/", l, r, parent_prec, format_expr)
  }
}
