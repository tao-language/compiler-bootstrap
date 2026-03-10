// ============================================================================
// CALCULATOR EXAMPLE - Using Grammar-Derived Formatter
// ============================================================================
import gleam/int
import gleam/result
import syntax/formatter.{type Doc, text, concat, hardline, line, nest, group, render, render_default, format_binop_auto, format_unary, format_unary_postfix, format_wrapped, format_list, format_application, format_lambda, format_record, format_record_auto, format_match, format_case, format_inline, format_soft_break, format_hard_break}
import syntax/grammar.{type Grammar, AstValue, ParensValue, TokenValue}

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
  let error_ast = Int(0)  // Dummy error value
  grammar.parse(calc_grammar(), source, error_ast)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0) |> formatter.render_default
}

/// Format expression using metadata-aware combinators.
///
/// Precedence is defined ONCE in grammar, used automatically.
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n) -> text(int.to_string(n))
    
    Add(l, r) ->
      format_binop_auto(
        format_expr,  // Pass formatter recursively
        l,
        r,
        "+",  // ← Operator separator
        10,  // Precedence from grammar (Add has prec 10)
        parent_prec,
      )
    
    Sub(l, r) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "-",  // ← Operator separator
        10,  // Precedence from grammar (Sub has prec 10)
        parent_prec,
      )
    
    Mul(l, r) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "*",  // ← Operator separator
        20,  // Precedence from grammar (Mul has prec 20)
        parent_prec,
      )
    
    Div(l, r) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "/",  // ← Operator separator
        20,  // Precedence from grammar (Div has prec 20)
        parent_prec,
      )
  }
}
