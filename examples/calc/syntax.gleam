// ============================================================================
// CALCULATOR GRAMMAR - Using Unified Grammar System
// ============================================================================
/// Calculator language demonstrating the unified grammar system:
/// - Single source of truth (grammar)
/// - Automatic parser generation
/// - Automatic formatter generation
/// - Correct precedence and associativity
import examples/calc/ast.{type Expr, Add, Div, Int, Mul, Sub}
import syntax/grammar.{type Grammar, type Value}

pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.token("Operator")
  // expr -> term (('+' | '-') term)*
  |> grammar.left_assoc(
    "Expr",
    "Term",
    [
      grammar.op("+", Add, 10),
      grammar.op("-", Sub, 10),
    ],
    10,
  )
  // term -> factor (('*' | '/') factor)*
  |> grammar.left_assoc(
    "Term",
    "Factor",
    [
      grammar.op("*", Mul, 20),
      grammar.op("/", Div, 20),
    ],
    20,
  )
  // factor -> NUMBER | '(' expr ')'
  |> grammar.rule("Factor", [
    grammar.alt(grammar.token("Number"), fn(values) {
      case values {
        [TokenValue(token)] -> Int(int_parse(token.value))
        _ -> panic as "Expected Number token"
      }
    }),
    grammar.alt(grammar.parenthesized("Expr"), fn(values) {
      case values {
        [ParensValue([AstValue(expr)])] -> expr
        _ -> panic as "Expected parenthesized expression"
      }
    }),
  ])
}

fn int_parse(s: String) -> Int {
  case int.parse(s) {
    Ok(n) -> n
    Error(_) -> 0
  }
}

// Import the Value type for pattern matching
import syntax/grammar.{AstValue, ParensValue, TokenValue}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  grammar.parse(calc_grammar(), source)
}

pub fn format(ast: Expr) -> String {
  grammar.format(calc_grammar(), ast)
}
