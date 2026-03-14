// ============================================================================
// TAO SYNTAX
// ============================================================================
/// Tao language grammar using the syntax library.
///
/// Expression language with overloading support.
///
/// For detailed documentation see:
/// - [Syntax Library](../../docs/syntax-library.md)
/// - [Tao Overloading](../../docs/plans/tao/10-overloading-design.md)
import tao/lexer
import gleam/int
import gleam/list
import gleam/result
import gleam/string
import gleam/option.{Some, None}
import syntax/grammar.{
  type Grammar, type ParseResult, type Span, Span, Grammar, type Value, AstValue,
  ParensValue, TokenValue, ListValue,
  InfixLeft,
  rule, alt, token_pattern, parenthesized, seq, ref, keyword_pattern, many, opt,
  infix_binary, left_assoc_rule,
  span_from_values, span_from_token, parse as grammar_parse,
}

// ============================================================================
// EXPRESSION AST
// ============================================================================
/// Expression for Tao with overloading support.
///
/// Supports: Arithmetic expressions, variables, comparison operators, and overloaded operators
pub type Expr {
  Int(value: Int, span: Span)
  Var(name: String, span: Span)
  Add(left: Expr, right: Expr, span: Span)
  Sub(left: Expr, right: Expr, span: Span)
  Mul(left: Expr, right: Expr, span: Span)
  Div(left: Expr, right: Expr, span: Span)
  /// Comparison operators
  Eq(left: Expr, right: Expr, span: Span)
  Neq(left: Expr, right: Expr, span: Span)
  Lt(left: Expr, right: Expr, span: Span)
  Gt(left: Expr, right: Expr, span: Span)
  Lte(left: Expr, right: Expr, span: Span)
  Gte(left: Expr, right: Expr, span: Span)
  /// Logical operators
  And(left: Expr, right: Expr, span: Span)
  Or(left: Expr, right: Expr, span: Span)
  Not(expr: Expr, span: Span)
  /// Overloaded function definition (e.g., fn (+)(x: I32) -> I32 { ... })
  OverloadedFn(
    name: String,
    type_param: String,
    param_name: String,
    param_type: String,
    return_type: String,
    body: Expr,
    span: Span,
  )
  /// Application with potential implicit type args
  OverloadedApp(name: String, args: List(Expr), span: Span)
}

// ============================================================================
// SPAN HELPERS
// ============================================================================

fn merge_spans(left: Span, right: Span) -> Span {
  Span(
    file: left.file,
    start_line: left.start_line,
    start_col: left.start_col,
    end_line: right.end_line,
    end_col: right.end_col,
  )
}

fn make_int(values) -> Expr {
  case values {
    [TokenValue(token)] ->
      Int(
        int.parse(token.value) |> result.unwrap(0),
        span_from_token(token, "tao"),
      )
    _ -> panic as "Expected number"
  }
}

fn make_var(values) -> Expr {
  case values {
    [TokenValue(token)] ->
      Var(token.value, span_from_token(token, "tao"))
    _ -> panic as "Expected identifier"
  }
}

fn make_add(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Add(left, right, span)
}

fn make_sub(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Sub(left, right, span)
}

fn make_mul(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Mul(left, right, span)
}

fn make_div(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Div(left, right, span)
}

fn make_eq(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Eq(left, right, span)
}

fn make_neq(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Neq(left, right, span)
}

fn make_lt(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Lt(left, right, span)
}

fn make_gt(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Gt(left, right, span)
}

fn make_lte(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Lte(left, right, span)
}

fn make_gte(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Gte(left, right, span)
}

fn make_and(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  And(left, right, span)
}

fn make_or(left: Expr, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  Or(left, right, span)
}

fn make_not(expr: Expr) -> Expr {
  Not(expr, get_span(expr))
}

fn ast_to_expr(ast) -> Expr {
  case ast {
    AstValue(e) -> e
    _ -> panic as "Expected expr"
  }
}

fn todo_ast() -> Value(Expr) {
  AstValue(Int(0, Span("todo", 0, 0, 0, 0)))
}

fn get_span(expr: Expr) -> Span {
  case expr {
    Int(_, span) -> span
    Var(_, span) -> span
    Add(_, _, span) -> span
    Sub(_, _, span) -> span
    Mul(_, _, span) -> span
    Div(_, _, span) -> span
    Eq(_, _, span) -> span
    Neq(_, _, span) -> span
    Lt(_, _, span) -> span
    Gt(_, _, span) -> span
    Lte(_, _, span) -> span
    Gte(_, _, span) -> span
    And(_, _, span) -> span
    Or(_, _, span) -> span
    Not(_, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
  }
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

/// Define the Tao grammar.
pub fn tao_grammar() -> Grammar(Expr) {
  Grammar(
    name: "Tao",
    start: "Program",
    tokens: ["Ident", "Number", "LParen", "RParen", "LBrace", "RBrace", "Colon", "Arrow"],
    keywords: ["fn", "let", "mut", "match", "if", "else", "type", "import", "export", "as", "comptime", "true", "false"],
    operators: [
      // Logical operators (precedence 3)
      infix_binary("&&", make_and, InfixLeft, 3, " && "),
      infix_binary("||", make_or, InfixLeft, 3, " || "),
      // Comparison operators (precedence 5)
      infix_binary("==", make_eq, InfixLeft, 5, " == "),
      infix_binary("!=", make_neq, InfixLeft, 5, " != "),
      infix_binary("<", make_lt, InfixLeft, 5, " < "),
      infix_binary(">", make_gt, InfixLeft, 5, " > "),
      infix_binary("<=", make_lte, InfixLeft, 5, " <= "),
      infix_binary(">=", make_gte, InfixLeft, 5, " >= "),
      // Arithmetic operators (precedence 10-20)
      infix_binary("+", make_add, InfixLeft, 10, " + "),
      infix_binary("-", make_sub, InfixLeft, 10, " - "),
      infix_binary("*", make_mul, InfixLeft, 20, " * "),
      infix_binary("/", make_div, InfixLeft, 20, " / "),
    ],
    rules: [
      // Program = Stmt*
      rule("Program", [
        alt(
          many(ref("Stmt")),
          fn(values) {
            case values {
              [ListValue(stmts)] -> {
                case list.first(stmts) {
                  Ok(AstValue(e)) -> e
                  _ -> Int(0, Span("empty", 0, 0, 0, 0))
                }
              }
              _ -> Int(0, Span("empty", 0, 0, 0, 0))
            }
          },
        ),
      ]),
      // Stmt = Fn | Expr (top-level expression)
      rule("Stmt", [
        alt(ref("OverloadedFn"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        alt(ref("Expr"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
      ]),
      // OverloadedFn = "fn" "(" Ident ")" "(" Ident ":" Type ")" "->" Type "{" Expr "}"
      rule("OverloadedFn", [
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // operator name
            token_pattern("RParen"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // param name
            token_pattern("Colon"),
            token_pattern("Ident"),  // param type
            token_pattern("RParen"),
            token_pattern("Arrow"),
            token_pattern("Ident"),  // return type
            ref("Expr"),             // body
          ]),
          make_overloaded_fn,
        ),
      ]),
      // Logic level: && and || (precedence 3)
      left_assoc_rule(
        "Logic",
        "Comparison",
        [
          infix_binary("&&", make_and, InfixLeft, 3, " && "),
          infix_binary("||", make_or, InfixLeft, 3, " || "),
        ],
        3,
      ),
      // Comparison level: ==, !=, <, >, <=, >= (precedence 5)
      left_assoc_rule(
        "Comparison",
        "Term",
        [
          infix_binary("==", make_eq, InfixLeft, 5, " == "),
          infix_binary("!=", make_neq, InfixLeft, 5, " != "),
          infix_binary("<", make_lt, InfixLeft, 5, " < "),
          infix_binary(">", make_gt, InfixLeft, 5, " > "),
          infix_binary("<=", make_lte, InfixLeft, 5, " <= "),
          infix_binary(">=", make_gte, InfixLeft, 5, " >= "),
        ],
        5,
      ),
      // Term level: * and / (precedence 20)
      left_assoc_rule(
        "Term",
        "Unary",
        [
          infix_binary("*", make_mul, InfixLeft, 20, " * "),
          infix_binary("/", make_div, InfixLeft, 20, " / "),
        ],
        20,
      ),
      // Expr level: + and - (precedence 10) - TOP LEVEL
      left_assoc_rule(
        "Expr",
        "Term",
        [
          infix_binary("+", make_add, InfixLeft, 10, " + "),
          infix_binary("-", make_sub, InfixLeft, 10, " - "),
        ],
        10,
      ),
      // Unary operators (prefix)
      rule("Unary", [
        alt(
          seq([
            keyword_pattern("!"),
            ref("Primary"),
          ]),
          fn(values) {
            case values {
              [_, AstValue(expr)] -> make_not(expr)
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(ref("Primary"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      rule("Primary", [
        alt(
          token_pattern("Number"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_int([TokenValue(token)])
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(
          token_pattern("Ident"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_var([TokenValue(token)])
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(
          parenthesized("Expr"),
          fn(values) {
            case values {
              [ParensValue([AstValue(expr)])] -> expr
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
      ]),
    ],
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

/// Get span from expression.
pub fn get_expr_span(expr: Expr) -> Span {
  case expr {
    Int(_, span) -> span
    Var(_, span) -> span
    Add(_, _, span) -> span
    Sub(_, _, span) -> span
    Mul(_, _, span) -> span
    Div(_, _, span) -> span
    Eq(_, _, span) -> span
    Neq(_, _, span) -> span
    Lt(_, _, span) -> span
    Gt(_, _, span) -> span
    Lte(_, _, span) -> span
    Gte(_, _, span) -> span
    And(_, _, span) -> span
    Or(_, _, span) -> span
    Not(_, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
  }
}

/// Parse Tao source code.
pub fn parse(source: String) -> ParseResult(Expr) {
  let error_ast = Int(0, Span("tao", 0, 0, 0, 0))
  grammar_parse(tao_grammar(), source, error_ast)
}

/// Helper to create overloaded function AST.
fn make_overloaded_fn(values) -> Expr {
  case values {
    [
      _,  // "fn"
      _,  // "("
      TokenValue(name_token),  // operator name
      _,  // ")"
      _,  // "("
      TokenValue(param_name_token),  // param name
      _,  // ":"
      TokenValue(param_type_token),  // param type
      _,  // ")"
      _,  // "->"
      TokenValue(return_type_token),  // return type
      AstValue(body),  // body
    ] -> OverloadedFn(
      name_token.value,
      "T",  // type param (simplified for now)
      param_name_token.value,
      param_type_token.value,
      return_type_token.value,
      body,
      span_from_token(name_token, "tao"),
    )
    _ -> panic as "Expected overloaded function definition"
  }
}

/// Format expression to string.
pub fn format_expr(expr: Expr) -> String {
  format_expr_loop(expr, 0)
}

fn format_expr_loop(expr: Expr, parent_prec: Int) -> String {
  case expr {
    Int(n, _) -> int.to_string(n)
    Var(name, _) -> name
    Add(l, r, _) -> format_binop(l, r, "+", 10, parent_prec)
    Sub(l, r, _) -> format_binop(l, r, "-", 10, parent_prec)
    Mul(l, r, _) -> format_binop(l, r, "*", 20, parent_prec)
    Div(l, r, _) -> format_binop(l, r, "/", 20, parent_prec)
    Eq(l, r, _) -> format_binop(l, r, "==", 5, parent_prec)
    Neq(l, r, _) -> format_binop(l, r, "!=", 5, parent_prec)
    Lt(l, r, _) -> format_binop(l, r, "<", 5, parent_prec)
    Gt(l, r, _) -> format_binop(l, r, ">", 5, parent_prec)
    Lte(l, r, _) -> format_binop(l, r, "<=", 5, parent_prec)
    Gte(l, r, _) -> format_binop(l, r, ">=", 5, parent_prec)
    And(l, r, _) -> format_binop(l, r, "&&", 3, parent_prec)
    Or(l, r, _) -> format_binop(l, r, "||", 3, parent_prec)
    Not(e, _) -> "!" <> format_expr_loop(e, 100)
    OverloadedFn(name, _type_param, param_name, param_type, _return_type, _body, _) -> {
      "fn (" <> name <> ")(" <> param_name <> ": " <> param_type <> ") -> " <> param_type <> " { ... }"
    }
    OverloadedApp(name, args, _) -> {
      name <> "(" <> string_join(list.map(args, format_expr), ", ") <> ")"
    }
  }
}

fn format_binop(left: Expr, right: Expr, op: String, prec: Int, parent_prec: Int) -> String {
  let need_parens = prec < parent_prec
  let result = format_expr_loop(left, prec) <> " " <> op <> " " <> format_expr_loop(right, prec + 1)
  case need_parens {
    True -> "(" <> result <> ")"
    False -> result
  }
}

fn string_join(strings: List(String), sep: String) -> String {
  case strings {
    [] -> ""
    [first] -> first
    [first, ..rest] -> first <> sep <> string_join(rest, sep)
  }
}
