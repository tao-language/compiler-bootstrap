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
      grammar.op("+", Add, 10, grammar.default_op_layout("+")),
      grammar.op("-", Sub, 10, grammar.default_op_layout("-")),
    ],
    10,
  )
  |> grammar.left_assoc(
    "Term",
    "Factor",
    [
      grammar.op("*", Mul, 20, grammar.default_op_layout("*")),
      grammar.op("/", Div, 20, grammar.default_op_layout("/")),
    ],
    20,
  )
  |> grammar.rule("Factor", [
    grammar.alt(
      grammar.token_pattern("Number"),
      fn(values) {
        case values {
          [TokenValue(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
          _ -> panic as "Expected Number"
        }
      },
      fn(ast, _) {
        case ast {
          Int(n) -> formatter.text(int.to_string(n))
          _ -> formatter.text("<num>")
        }
      },
    ),
    grammar.alt(
      grammar.parenthesized("Expr"),
      fn(values) {
        case values {
          [ParensValue([AstValue(expr)])] -> expr
          _ -> panic as "Expected parenthesized expr"
        }
      },
      fn(ast, prec) { format_expr(ast, prec) },
    ),
  ])
}

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, -1) |> formatter.render_default
}

fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> formatter.text(int.to_string(n))
    Add(l, r) ->
      format_binop(
        format_expr(l, 10),
        format_expr(r, 11),
        " + ",
        10,
        parent_prec,
      )
    Sub(l, r) ->
      format_binop(
        format_expr(l, 10),
        format_expr(r, 11),
        " - ",
        10,
        parent_prec,
      )
    Mul(l, r) ->
      format_binop(
        format_expr(l, 20),
        format_expr(r, 21),
        " * ",
        20,
        parent_prec,
      )
    Div(l, r) ->
      format_binop(
        format_expr(l, 20),
        format_expr(r, 21),
        " / ",
        20,
        parent_prec,
      )
  }
}

fn format_binop(
  left: Doc,
  right: Doc,
  op: String,
  prec: Int,
  parent_prec: Int,
) -> Doc {
  let doc = formatter.concat([left, formatter.text(op), right])
  case prec < parent_prec {
    True -> formatter.parens(doc)
    False -> doc
  }
}
