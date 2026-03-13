// ============================================================================
// TAO SYNTAX - MVP
// ============================================================================
/// Tao language grammar using the syntax library.
///
/// MVP: Simple expression language with functions.
///
/// For detailed documentation see:
/// - [Syntax Library](../../docs/syntax-library.md)
/// - [Tao MVP Plan](../../docs/plans/tao/09-tao-mvp-plan.md)
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
// EXPRESSION AST (MVP)
// ============================================================================
/// Simple expression for MVP testing.
pub type MvpExpr {
  MvpInt(value: Int, span: Span)
  MvpVar(name: String, span: Span)
  MvpAdd(left: MvpExpr, right: MvpExpr, span: Span)
  MvpSub(left: MvpExpr, right: MvpExpr, span: Span)
  MvpMul(left: MvpExpr, right: MvpExpr, span: Span)
  MvpDiv(left: MvpExpr, right: MvpExpr, span: Span)
  MvpCall(name: String, args: List(MvpExpr), span: Span)
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

fn make_call(values) -> MvpExpr {
  case values {
    [TokenValue(name), _, args_value, _] -> {
      let args = case args_value {
        ListValue(asts) -> list.map(asts, ast_to_expr)
        _ -> []
      }
      MvpCall(name.value, args, span_from_token(name, "tao"))
    }
    _ -> panic as "Expected call"
  }
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
    MvpCall(_, _, span) -> span
  }
}

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

/// Define the Tao grammar (MVP).
pub fn tao_grammar() -> Grammar(MvpExpr) {
  Grammar(
    name: "Tao",
    start: "Expr",
    tokens: ["Ident", "Number", "LParen", "RParen", "LBrace", "RBrace"],
    keywords: lexer.keywords,
    operators: [
      infix_binary("+", make_add, InfixLeft, 10, " + "),
      infix_binary("-", make_sub, InfixLeft, 10, " - "),
      infix_binary("*", make_mul, InfixLeft, 20, " * "),
      infix_binary("/", make_div, InfixLeft, 20, " / "),
    ],
    rules: [
      left_assoc_rule(
        "Expr",
        "Primary",
        [
          infix_binary("+", make_add, InfixLeft, 10, " + "),
          infix_binary("-", make_sub, InfixLeft, 10, " - "),
        ],
        10,
      ),
      left_assoc_rule(
        "Term",
        "Factor",
        [
          infix_binary("*", make_mul, InfixLeft, 20, " * "),
          infix_binary("/", make_div, InfixLeft, 20, " / "),
        ],
        20,
      ),
      rule("Primary", [
        alt(token_pattern("Number"), make_int),
        alt(token_pattern("Ident"), make_var),
        alt(parenthesized("Expr"), fn(values) {
          case values {
            [ParensValue([AstValue(expr)])] -> expr
            _ -> panic as "Expected (expr)"
          }
        }),
        alt(ref("Call"), fn(values) {
          case values {
            [AstValue(expr)] -> expr
            _ -> panic as "Expected call"
          }
        }),
      ]),
      rule("Call", [
        alt(
          seq([
            token_pattern("Ident"),
            token_pattern("LParen"),
            many(seq([ref("Expr"), token_pattern("Comma")])),
            opt(ref("Expr")),
            token_pattern("RParen"),
          ]),
          fn(values) {
            case values {
              [TokenValue(name), _, ListValue(pairs), last_opt, _] -> {
                let args_from_pairs = list.flat_map(pairs, fn(pair_val) {
                  case pair_val {
                    ListValue(items) -> {
                      case list.first(items) {
                        Ok(AstValue(e)) -> [e]
                        _ -> []
                      }
                    }
                    _ -> []
                  }
                })
                let last_arg = case last_opt {
                  AstValue(e) -> [e]
                  _ -> []
                }
                MvpCall(name.value, list.append(args_from_pairs, last_arg), span_from_token(name, "tao"))
              }
              _ -> panic as "Expected call"
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

/// Parse Tao source code (MVP).
pub fn parse(source: String) -> ParseResult(MvpExpr) {
  let error_ast = MvpInt(0, Span("tao", 0, 0, 0, 0))
  grammar_parse(tao_grammar(), source, error_ast)
}

/// Format MVP expression to string.
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
    MvpCall(name, args, _) -> {
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
