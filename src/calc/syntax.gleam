// ============================================================================
// CALCULATOR SYNTAX - Grammar Definition
// ============================================================================

/// Calculator language with +, *, and parentheses
/// 
/// Demonstrates the generic grammar system with:
/// - Left-associative operators
/// - Operator precedence
/// - Automatic parser generation
/// - AST-specific formatting using grammar precedence
import calc/ast.{type Expr, Add, Int, Mul}
import gleam/int
import gleam/result
import grammar.{type Grammar, type ParseChild, ChildAST, ChildToken}
import parser.{type ParseResult}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

pub fn calc_grammar() -> Grammar(Expr) {
  grammar.new()
  |> grammar.start("Expr")
  |> grammar.with_token("Number")
  |> grammar.with_token("Operator")
  |> grammar.with_token("LParen")
  |> grammar.with_token("RParen")
  // expr -> term (('+' | '-') term)*
  // Left-associative with precedence 10
  |> grammar.left_assoc(
    "Expr",
    grammar.ref("Term"),
    [
      grammar.op("+", fn(l, r) { Add(l, r) }, " + "),
    ],
    10,
  )
  // term -> factor (('*' | '/') factor)*
  // Left-associative with precedence 20 (binds tighter than +)
  |> grammar.left_assoc(
    "Term",
    grammar.ref("Factor"),
    [
      grammar.op("*", fn(l, r) { Mul(l, r) }, " * "),
    ],
    20,
  )
  // factor -> NUMBER | '(' expr ')'
  |> grammar.rule(
    "Factor",
    grammar.choice([
      grammar.token("Number"),
      grammar.seq([
        grammar.token("LParen"),
        grammar.ref("Expr"),
        grammar.token("RParen"),
      ]),
    ]),
    fn(children) {
      case children {
        [ChildToken(token)] -> Int(int.parse(token.value) |> result.unwrap(0))
        [_, ChildAST(expr), _] -> expr
        _ -> panic as "Invalid factor"
      }
    },
    30,
    // Highest precedence for atoms
    grammar.TemplateSeq([]),
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn parse(source: String) -> ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0)
}

// ============================================================================
// FORMATTER - AST-specific using grammar precedence
// ============================================================================

fn format_expr(expr: Expr, parent_prec: Int) -> String {
  case expr {
    Int(n) -> int.to_string(n)
    Add(l, r) -> {
      let prec = 10
      let s = format_expr(l, prec) <> " + " <> format_expr(r, prec + 1)
      case prec < parent_prec {
        True -> "(" <> s <> ")"
        False -> s
      }
    }
    Mul(l, r) -> {
      let prec = 20
      let s = format_expr(l, prec) <> " * " <> format_expr(r, prec + 1)
      case prec < parent_prec {
        True -> "(" <> s <> ")"
        False -> s
      }
    }
  }
}
