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
pub type MvpExpr {
  MvpInt(value: Int, span: Span)
  MvpVar(name: String, span: Span)
  MvpAdd(left: MvpExpr, right: MvpExpr, span: Span)
  MvpSub(left: MvpExpr, right: MvpExpr, span: Span)
  MvpMul(left: MvpExpr, right: MvpExpr, span: Span)
  MvpDiv(left: MvpExpr, right: MvpExpr, span: Span)
  /// Comparison operators
  MvpEq(left: MvpExpr, right: MvpExpr, span: Span)
  MvpNeq(left: MvpExpr, right: MvpExpr, span: Span)
  MvpLt(left: MvpExpr, right: MvpExpr, span: Span)
  MvpGt(left: MvpExpr, right: MvpExpr, span: Span)
  MvpLte(left: MvpExpr, right: MvpExpr, span: Span)
  MvpGte(left: MvpExpr, right: MvpExpr, span: Span)
  /// Logical operators
  MvpAnd(left: MvpExpr, right: MvpExpr, span: Span)
  MvpOr(left: MvpExpr, right: MvpExpr, span: Span)
  MvpNot(expr: MvpExpr, span: Span)
  /// Overloaded function definition (e.g., fn (+)(x: I32) -> I32 { ... })
  OverloadedFn(
    name: String,
    type_param: String,
    param_name: String,
    param_type: String,
    return_type: String,
    body: MvpExpr,
    span: Span,
  )
  /// Application with potential implicit type args
  OverloadedApp(name: String, args: List(MvpExpr), span: Span)
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

fn make_int(values) -> MvpExpr {
  case values {
    [TokenValue(token)] ->
      MvpInt(
        int.parse(token.value) |> result.unwrap(0),
        span_from_token(token, "tao"),
      )
    _ -> panic as "Expected number"
  }
}

fn make_var(values) -> MvpExpr {
  case values {
    [TokenValue(token)] ->
      MvpVar(token.value, span_from_token(token, "tao"))
    _ -> panic as "Expected identifier"
  }
}

fn make_add(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpAdd(left, right, span)
}

fn make_sub(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpSub(left, right, span)
}

fn make_mul(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpMul(left, right, span)
}

fn make_div(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpDiv(left, right, span)
}

fn make_eq(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpEq(left, right, span)
}

fn make_neq(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpNeq(left, right, span)
}

fn make_lt(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpLt(left, right, span)
}

fn make_gt(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpGt(left, right, span)
}

fn make_lte(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpLte(left, right, span)
}

fn make_gte(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpGte(left, right, span)
}

fn make_and(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpAnd(left, right, span)
}

fn make_or(left: MvpExpr, right: MvpExpr) -> MvpExpr {
  let span = merge_spans(get_span(left), get_span(right))
  MvpOr(left, right, span)
}

fn make_not(expr: MvpExpr) -> MvpExpr {
  MvpNot(expr, get_span(expr))
}

fn ast_to_expr(ast) -> MvpExpr {
  case ast {
    AstValue(e) -> e
    _ -> panic as "Expected expr"
  }
}

fn todo_ast() -> Value(MvpExpr) {
  AstValue(MvpInt(0, Span("todo", 0, 0, 0, 0)))
}

fn get_span(expr: MvpExpr) -> Span {
  case expr {
    MvpInt(_, span) -> span
    MvpVar(_, span) -> span
    MvpAdd(_, _, span) -> span
    MvpSub(_, _, span) -> span
    MvpMul(_, _, span) -> span
    MvpDiv(_, _, span) -> span
    MvpEq(_, _, span) -> span
    MvpNeq(_, _, span) -> span
    MvpLt(_, _, span) -> span
    MvpGt(_, _, span) -> span
    MvpLte(_, _, span) -> span
    MvpGte(_, _, span) -> span
    MvpAnd(_, _, span) -> span
    MvpOr(_, _, span) -> span
    MvpNot(_, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
  }
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

/// Define the Tao grammar.
pub fn tao_grammar() -> Grammar(MvpExpr) {
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
                  _ -> MvpInt(0, Span("empty", 0, 0, 0, 0))
                }
              }
              _ -> MvpInt(0, Span("empty", 0, 0, 0, 0))
            }
          },
        ),
      ]),
      // Stmt = Fn | Expr (top-level expression)
      rule("Stmt", [
        alt(ref("OverloadedFn"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> MvpInt(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        alt(ref("Expr"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> MvpInt(0, Span("empty", 0, 0, 0, 0))
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
              _ -> MvpInt(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(ref("Primary"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> MvpInt(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      rule("Primary", [
        alt(
          token_pattern("Number"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_int([TokenValue(token)])
              _ -> MvpInt(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(
          token_pattern("Ident"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_var([TokenValue(token)])
              _ -> MvpInt(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        alt(
          parenthesized("Expr"),
          fn(values) {
            case values {
              [ParensValue([AstValue(expr)])] -> expr
              _ -> MvpInt(0, Span("error", 0, 0, 0, 0))
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
pub fn get_expr_span(expr: MvpExpr) -> Span {
  case expr {
    MvpInt(_, span) -> span
    MvpVar(_, span) -> span
    MvpAdd(_, _, span) -> span
    MvpSub(_, _, span) -> span
    MvpMul(_, _, span) -> span
    MvpDiv(_, _, span) -> span
    MvpEq(_, _, span) -> span
    MvpNeq(_, _, span) -> span
    MvpLt(_, _, span) -> span
    MvpGt(_, _, span) -> span
    MvpLte(_, _, span) -> span
    MvpGte(_, _, span) -> span
    MvpAnd(_, _, span) -> span
    MvpOr(_, _, span) -> span
    MvpNot(_, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
  }
}

/// Parse Tao source code.
pub fn parse(source: String) -> ParseResult(MvpExpr) {
  let error_ast = MvpInt(0, Span("tao", 0, 0, 0, 0))
  grammar_parse(tao_grammar(), source, error_ast)
}

/// Helper to create overloaded function AST.
fn make_overloaded_fn(values) -> MvpExpr {
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
pub fn format_expr(expr: MvpExpr) -> String {
  format_expr_loop(expr, 0)
}

fn format_expr_loop(expr: MvpExpr, parent_prec: Int) -> String {
  case expr {
    MvpInt(n, _) -> int.to_string(n)
    MvpVar(name, _) -> name
    MvpAdd(l, r, _) -> format_binop(l, r, "+", 10, parent_prec)
    MvpSub(l, r, _) -> format_binop(l, r, "-", 10, parent_prec)
    MvpMul(l, r, _) -> format_binop(l, r, "*", 20, parent_prec)
    MvpDiv(l, r, _) -> format_binop(l, r, "/", 20, parent_prec)
    MvpEq(l, r, _) -> format_binop(l, r, "==", 5, parent_prec)
    MvpNeq(l, r, _) -> format_binop(l, r, "!=", 5, parent_prec)
    MvpLt(l, r, _) -> format_binop(l, r, "<", 5, parent_prec)
    MvpGt(l, r, _) -> format_binop(l, r, ">", 5, parent_prec)
    MvpLte(l, r, _) -> format_binop(l, r, "<=", 5, parent_prec)
    MvpGte(l, r, _) -> format_binop(l, r, ">=", 5, parent_prec)
    MvpAnd(l, r, _) -> format_binop(l, r, "&&", 3, parent_prec)
    MvpOr(l, r, _) -> format_binop(l, r, "||", 3, parent_prec)
    MvpNot(e, _) -> "!" <> format_expr_loop(e, 100)
    OverloadedFn(name, type_param, param_name, param_type, return_type, _body, _) -> {
      "fn (" <> name <> ")(" <> param_name <> ": " <> param_type <> ") -> " <> return_type <> " { ... }"
    }
    OverloadedApp(name, args, _) -> {
      name <> "(" <> string_join(list.map(args, format_expr), ", ") <> ")"
    }
  }
}

fn format_binop(left: MvpExpr, right: MvpExpr, op: String, prec: Int, parent_prec: Int) -> String {
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
