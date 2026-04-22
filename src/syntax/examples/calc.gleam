// ============================================================================
// CALCULATOR EXAMPLE - Operator Metadata Query API
// ============================================================================
/// Calculator example demonstrating grammar-derived parsing and formatting
/// with operator metadata query API.
///
/// For detailed documentation see:
/// - [Operator Metadata Query API Plan](../../docs/plans/syntax/09-operator-metadata-query-api.md)
import gleam/int
import gleam/result
import gleam/string
import syntax/formatter.{type Doc, concat, format_binop_auto, text}
import syntax/grammar.{
  type Grammar, type Span, AstValue, ParensValue, TokenValue,
  InfixLeft,
  left_assoc_rule, rule, alt, token_pattern, parenthesized, seq, ref, keyword_pattern, many,
  infix_binary, prefix, postfix, get_operator_precedence,
}
import syntax/lexer.{type Token}

// ============================================================================
// TYPES
// ============================================================================

/// Calculator expression with source location tracking.
/// Each constructor includes a span for error reporting.
pub type Expr {
  /// Integer literal
  Int(value: Int, span: Span)
  /// Addition
  Add(left: Expr, right: Expr, span: Span)
  /// Subtraction
  Sub(left: Expr, right: Expr, span: Span)
  /// Multiplication
  Mul(left: Expr, right: Expr, span: Span)
  /// Division
  Div(left: Expr, right: Expr, span: Span)
  /// Negation (prefix)
  Neg(expr: Expr, span: Span)
  /// Factorial (postfix)
  Fact(expr: Expr, span: Span)
}

// ============================================================================
// GRAMMAR
// ============================================================================

/// Build an Add expression with span from left and right operands.
fn make_add(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Add(left, right, span)
}

/// Build a Sub expression with span from left and right operands.
fn make_sub(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Sub(left, right, span)
}

/// Build a Mul expression with span from left and right operands.
fn make_mul(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Mul(left, right, span)
}

/// Build a Div expression with span from left and right operands.
fn make_div(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Div(left, right, span)
}

/// Build a Neg expression with span from operand.
fn make_neg(expr: Expr) -> Expr {
  let span = get_span(expr)
  Neg(expr, span)
}

/// Build a Fact expression with span from operand.
fn make_fact(expr: Expr) -> Expr {
  let span = get_span(expr)
  Fact(expr, span)
}

/// Fold multiple factorial operators from left to right.
fn fold_bangs(base: Expr, bangs: List(grammar.Value(Expr))) -> Expr {
  case bangs {
    [] -> base
    [_bang, ..rest] -> fold_bangs(make_fact(base), rest)
  }
}

/// Merge two spans to create a span covering both.
fn merge_spans(left: Span, right: Span) -> Span {
  grammar.Span(
    file: left.file,
    start_line: left.start_line,
    start_col: left.start_col,
    end_line: right.end_line,
    end_col: right.end_col,
  )
}

pub fn calc_grammar() -> Grammar(Expr) {
  grammar.Grammar(
    name: "Calc",
    start: "Expr",
    tokens: ["Number", "LParen", "RParen"],
    keywords: [],
    operators: [
      // Binary infix operators
      infix_binary("+", make_add, InfixLeft, 10, " + "),
      infix_binary("-", make_sub, InfixLeft, 10, " - "),
      infix_binary("*", make_mul, InfixLeft, 20, " * "),
      infix_binary("/", make_div, InfixLeft, 20, " / "),
      // Prefix operator
      prefix("-", make_neg, 100),
      // Postfix operator
      postfix("!", make_fact, 100),
    ],
    rules: [
      left_assoc_rule(
        "Expr",
        "Term",
        [
          infix_binary("+", make_add, InfixLeft, 10, " + "),
          infix_binary("-", make_sub, InfixLeft, 10, " - "),
        ],
        10,
      ),
      left_assoc_rule(
        "Term",
        "Unary",
        [
          infix_binary("*", make_mul, InfixLeft, 20, " * "),
          infix_binary("/", make_div, InfixLeft, 20, " / "),
        ],
        20,
      ),
      rule("Unary", [
        // Prefix minus: -expr (can chain: --x)
        alt(
          seq([keyword_pattern("-"), ref("Unary")]),
          fn(values) {
            case values {
              [_, AstValue(e)] -> make_neg(e)
              _ -> panic as "Expected -expr"
            }
          },
        ),
        // Or Postfix (non-recursive ref)
        alt(
          ref("Postfix"),
          fn(values) {
            case values {
              [AstValue(e)] -> e
              _ -> panic as "Expected AstValue"
            }
          }
        ),
      ]),
      rule("Postfix", [
        // Factor followed by optional postfix operators
        alt(
          seq([ref("Factor"), many(keyword_pattern("!"))]),
          fn(values) {
            // values = [Factor, !, !, ...] or [Factor] or [Factor, !]
            case values {
              [first, ..rest] -> {
                case first {
                  AstValue(base) -> fold_bangs(base, rest)
                  _ -> panic as "Expected AstValue as first value"
                }
              }
              _ -> panic as "Expected at least one value in Postfix rule"
            }
          }
        ),
      ]),
      rule("Factor", [
        alt(
          token_pattern("Number"),
          fn(values) {
            case values {
              [TokenValue(token)] ->
                Int(
                  int.parse(token.value) |> result.unwrap(0),
                  token_to_span(token),
                )
              _ -> panic as "Expected Number"
            }
          },
        ),
        alt(
          parenthesized("Expr"),
          fn(values) {
            case values {
              [ParensValue([AstValue(expr)])] -> expr
              _ -> panic as "Expected parenthesized expr"
            }
          },
        ),
      ]),
    ],
  )
}

// ============================================================================
// PARSER
// ============================================================================

pub fn parse(source: String) -> grammar.ParseResult(Expr) {
  let error_ast = Int(0, grammar.Span("", 0, 0, 0, 0))
  grammar.parse(calc_grammar(), source, error_ast)
}

// ============================================================================
// FORMATTER
// ============================================================================

pub fn format(ast: Expr) -> String {
  format_expr(ast, 0) |> formatter.render_default
}

/// Format expression using operator metadata from grammar.
///
/// Precedence is defined ONCE in grammar, queried automatically.
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  let grammar = calc_grammar()
  
  case ast {
    Int(n, _span) -> text(int.to_string(n))

    Add(l, r, _span) -> format_with_op(grammar, l, r, "+", parent_prec)
    Sub(l, r, _span) -> format_with_op(grammar, l, r, "-", parent_prec)
    Mul(l, r, _span) -> format_with_op(grammar, l, r, "*", parent_prec)
    Div(l, r, _span) -> format_with_op(grammar, l, r, "/", parent_prec)
    
    Neg(e, _span) -> {
      // Prefix operator: -e
      let prec = get_operator_precedence(grammar, "-")
      let operand_doc = format_expr(e, prec + 1)
      concat([text("-"), operand_doc])
    }
    
    Fact(e, _span) -> {
      // Postfix operator: e!
      let prec = get_operator_precedence(grammar, "!")
      let operand_doc = format_expr(e, prec + 1)
      concat([operand_doc, text("!")])
    }
  }
}

/// Format binary operator using metadata from grammar.
fn format_with_op(
  grammar: Grammar(Expr),
  l: Expr,
  r: Expr,
  symbol: String,
  parent_prec: Int,
) -> Doc {
  let prec = get_operator_precedence(grammar, symbol)
  format_binop_auto(format_expr, l, r, symbol, prec, parent_prec)
}

// ============================================================================
// HELPERS
// ============================================================================

/// Convert a token to a span for error reporting.
fn token_to_span(token: Token) -> Span {
  let value_len = token.value |> string.length
  grammar.Span(
    file: "input",
    start_line: token.line,
    start_col: token.column,
    end_line: token.line,
    end_col: token.column + value_len,
  )
}

/// Get the span from an expression for error reporting.
pub fn get_span(expr: Expr) -> Span {
  case expr {
    Int(_, span) -> span
    Add(_, _, span) -> span
    Sub(_, _, span) -> span
    Mul(_, _, span) -> span
    Div(_, _, span) -> span
    Neg(_, span) -> span
    Fact(_, span) -> span
  }
}
