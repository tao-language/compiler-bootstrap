// ============================================================================
// CALCULATOR SYNTAX - Grammar Definition with Formatting
// ============================================================================

/// Calculator language with +, *, and parentheses
///
/// Demonstrates the generic grammar system with:
/// - Left-associative operators
/// - Operator precedence
/// - Automatic parser generation
/// - Runtime formatter using grammar lookup
/// - Pretty-printing with formatter.gleam
import calc/ast.{type Expr, Add, Int, Mul}
import formatter.{type Doc}
import gleam/int
import gleam/result
import grammar.{
  type Grammar, type LayoutStyle, type ParseChild, ChildAST, ChildToken,
}
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
  // Left-associative with precedence 10, break after operator with 2-space indent
  |> grammar.left_assoc(
    "Expr",
    grammar.ref("Term"),
    [
      grammar.op(
        "+",
        fn(l, r) { Add(l, r) },
        " +",
        // No trailing space - formatter.line() adds it
        10,
        grammar.Left,
        grammar.BreakAfterOperator(2),
      ),
    ],
    10,
  )
  // term -> factor (('*' | '/') factor)*
  // Left-associative with precedence 20 (binds tighter than +)
  |> grammar.left_assoc(
    "Term",
    grammar.ref("Factor"),
    [
      grammar.op(
        "*",
        fn(l, r) { Mul(l, r) },
        " *",
        // No trailing space - formatter.line() adds it
        20,
        grammar.Left,
        grammar.BreakAfterOperator(2),
      ),
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
  let g = calc_grammar()
  let doc = format_expr(g, ast, -1)
  // -1 = no parent, never wrap parens
  formatter.render_default(doc)
}

// ============================================================================
// FORMATTER - Uses grammar lookup for operators
// ============================================================================

fn format_expr(g: Grammar(Expr), expr: Expr, parent_prec: Int) -> Doc {
  // Helper that captures grammar for recursive calls
  let format_child = fn(child: Expr, prec: Int) -> Doc {
    format_expr(g, child, prec)
  }

  case expr {
    Int(n) -> formatter.text(int.to_string(n))

    // Operators use grammar lookup - automatic precedence & layout!
    Add(l, r) -> grammar.format_op(g, "+", l, r, parent_prec, format_child)
    Mul(l, r) -> grammar.format_op(g, "*", l, r, parent_prec, format_child)
  }
}
