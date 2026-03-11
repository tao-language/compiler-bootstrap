// ============================================================================
// CALCULATOR EXAMPLE - Using Grammar-Derived Formatter with Spans
// ============================================================================
/// Calculator example demonstrating grammar-derived parsing and formatting
/// with source location tracking for error reporting.
///
/// For detailed documentation see:
/// - [Syntax Library](../../docs/syntax-library.md)
import gleam/int
import gleam/result
import gleam/string
import syntax/formatter.{type Doc, text, format_binop_auto}
import syntax/grammar.{type Grammar, type Span, AstValue, ParensValue, TokenValue}
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
      grammar.op("+", make_add, 10, grammar.default_op_layout("+")),
      grammar.op("-", make_sub, 10, grammar.default_op_layout("-")),
    ],
    10,
  )
  |> grammar.left_assoc(
    "Term",
    "Factor",
    [
      grammar.op("*", make_mul, 20, grammar.default_op_layout("*")),
      grammar.op("/", make_div, 20, grammar.default_op_layout("/")),
    ],
    20,
  )
  |> grammar.rule("Factor", [
    grammar.alt(
      grammar.token_pattern("Number"),
      fn(values) {
        case values {
          [TokenValue(token)] ->
            Int(int.parse(token.value) |> result.unwrap(0), token_to_span(token))
          _ -> panic as "Expected Number"
        }
      },
      fn(_ast, _prec) { formatter.text("") },
    ),
    grammar.alt(
      grammar.parenthesized("Expr"),
      fn(values) {
        case values {
          [ParensValue([AstValue(expr)])] -> expr
          _ -> panic as "Expected parenthesized expr"
        }
      },
      fn(_ast, _prec) { formatter.text("") },
    ),
  ])
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

/// Format expression using metadata-aware combinators.
///
/// Precedence is defined ONCE in grammar, used automatically.
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Int(n, _span) -> text(int.to_string(n))

    Add(l, r, _span) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "+",
        10,
        parent_prec,
      )

    Sub(l, r, _span) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "-",
        10,
        parent_prec,
      )

    Mul(l, r, _span) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "*",
        20,
        parent_prec,
      )

    Div(l, r, _span) ->
      format_binop_auto(
        format_expr,
        l,
        r,
        "/",
        20,
        parent_prec,
      )
  }
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
  }
}
