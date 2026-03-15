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
import tao/ast.{
  type Expr as AstExpr, Var as AstVar, Lit as AstLit, BinOp as AstBinOpExpr,
  UnaryOp as AstUnaryOp, Lambda as AstLambda, Call as AstCall,
  type BinOperator, OpAdd, OpSub, OpMul, OpDiv, OpEq, OpNeq, OpLt, OpGt, OpLte, OpGte, OpAnd, OpOr,
  type UnaryOperator, OpNot,
  Int as AstInt, type Param as AstParamType, Param as AstParam, TVar,
}
import tao/import_ast.{type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard, type ImportItem, ImportName, ImportType, ImportOperator}
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
  ParseResult as ParseResultVal,
}

// ============================================================================
// EXPRESSION AST
// ============================================================================
/// Expression for Tao with overloading support.
///
/// Supports: Arithmetic expressions, variables, comparison operators, and overloaded operators
///
/// Binary and unary operators are represented using enums to reduce constructor
/// explosion and make pattern matching more maintainable.

/// Binary operators for Tao expressions.
pub type BinOp {
  /// Arithmetic: +
  Add
  /// Arithmetic: -
  Sub
  /// Arithmetic: *
  Mul
  /// Arithmetic: /
  Div
  /// Comparison: ==
  Eq
  /// Comparison: !=
  Neq
  /// Comparison: <
  Lt
  /// Comparison: >
  Gt
  /// Comparison: <=
  Lte
  /// Comparison: >=
  Gte
  /// Logical: &&
  And
  /// Logical: ||
  Or
}

/// Unary operators for Tao expressions.
pub type UnaryOp {
  /// Logical: !
  Not
}

/// Expression for Tao with overloading support.
pub type Expr {
  /// Integer literal (e.g., 42)
  Int(value: Int, span: Span)
  /// Variable reference (e.g., x)
  Var(name: String, span: Span)
  /// Binary operation (e.g., x + y)
  BinOp(left: Expr, op: BinOp, right: Expr, span: Span)
  /// Unary operation (e.g., !x)
  UnaryOp(op: UnaryOp, expr: Expr, span: Span)
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
// CONVERSION TO AST.GLEAM
// ============================================================================
/// Convert syntax.Expr to ast.Expr for integration with the main AST.

pub fn expr_to_ast(expr: Expr) -> AstExpr {
  expr_to_ast_loop(expr)
}

fn expr_to_ast_loop(expr: Expr) -> AstExpr {
  case expr {
    Int(value, span) -> AstLit(AstInt(value), span)
    Var(name, span) -> AstVar(name, span)
    BinOp(left, op, right, span) -> {
      let ast_op = binop_to_ast(op)
      let ast_left = expr_to_ast_loop(left)
      let ast_right = expr_to_ast_loop(right)
      AstBinOpExpr(ast_left, ast_op, ast_right, span)
    }
    UnaryOp(op, expr, span) -> {
      let ast_op = unaryop_to_ast(op)
      let ast_expr = expr_to_ast_loop(expr)
      AstUnaryOp(ast_op, ast_expr, span)
    }
    OverloadedFn(name, type_param, param_name, param_type, return_type, body, span) -> {
      // Overloaded functions become Lambda in ast
      let ast_body = expr_to_ast_loop(body)
      AstLambda([type_param], [param(param_name, param_type, span)], ast_body, span)
    }
    OverloadedApp(name, args, span) -> {
      let ast_args = list.map(args, expr_to_ast_loop)
      AstCall(AstVar(name, span), ast_args, span)
    }
  }
}

fn binop_to_ast(op: BinOp) -> BinOperator {
  case op {
    Add -> OpAdd
    Sub -> OpSub
    Mul -> OpMul
    Div -> OpDiv
    Eq -> OpEq
    Neq -> OpNeq
    Lt -> OpLt
    Gt -> OpGt
    Lte -> OpLte
    Gte -> OpGte
    And -> OpAnd
    Or -> OpOr
  }
}

fn unaryop_to_ast(op: UnaryOp) -> UnaryOperator {
  case op {
    Not -> OpNot
  }
}

fn param(name: String, type_: String, span: Span) -> AstParamType {
  AstParam(name, Some(TVar(type_)), span)
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

fn make_not(expr: Expr) -> Expr {
  let span = get_expr_span(expr)
  UnaryOp(Not, expr, span)
}

fn make_binop(left: Expr, op: BinOp, right: Expr) -> Expr {
  let span = merge_spans(get_span(left), get_span(right))
  BinOp(left, op, right, span)
}

fn make_add(left: Expr, right: Expr) -> Expr {
  make_binop(left, Add, right)
}

fn make_sub(left: Expr, right: Expr) -> Expr {
  make_binop(left, Sub, right)
}

fn make_mul(left: Expr, right: Expr) -> Expr {
  make_binop(left, Mul, right)
}

fn make_div(left: Expr, right: Expr) -> Expr {
  make_binop(left, Div, right)
}

fn make_eq(left: Expr, right: Expr) -> Expr {
  make_binop(left, Eq, right)
}

fn make_neq(left: Expr, right: Expr) -> Expr {
  make_binop(left, Neq, right)
}

fn make_lt(left: Expr, right: Expr) -> Expr {
  make_binop(left, Lt, right)
}

fn make_gt(left: Expr, right: Expr) -> Expr {
  make_binop(left, Gt, right)
}

fn make_lte(left: Expr, right: Expr) -> Expr {
  make_binop(left, Lte, right)
}

fn make_gte(left: Expr, right: Expr) -> Expr {
  make_binop(left, Gte, right)
}

fn make_and(left: Expr, right: Expr) -> Expr {
  make_binop(left, And, right)
}

fn make_or(left: Expr, right: Expr) -> Expr {
  make_binop(left, Or, right)
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
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
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
    tokens: ["Ident", "Number", "LParen", "RParen", "LBrace", "RBrace", "Colon", "Arrow", "Slash", "Star", "Comma"],
    keywords: ["fn", "let", "mut", "match", "if", "else", "type", "import", "export", "as", "comptime", "true", "false", "for", "in", "while", "loop", "break", "continue", "return", "yield"],
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
                // Return first statement for now (Module parsing will be done separately)
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
      // Stmt = Import | Fn | Let | For | While | Loop | Break | Continue | Return | Yield | Expr
      rule("Stmt", [
        // Import statement
        alt(ref("Import"), fn(values) {
          case values {
            [_] -> Int(0, Span("import", 0, 0, 0, 0))
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Function definition
        alt(ref("Fn"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Let binding
        alt(ref("Let"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Expression statement
        alt(ref("Expr"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
      ]),
      // Import = "import" Path ("as" Ident)? ("{" Ident ("," Ident)* "}")?
      rule("Import", [
        alt(
          seq([
            keyword_pattern("import"),
            token_pattern("Ident"),  // path component
            many(seq([
              token_pattern("Slash"),
              token_pattern("Ident"),
            ])),
            opt(seq([
              keyword_pattern("as"),
              token_pattern("Ident"),  // alias
            ])),
            opt(seq([
              token_pattern("LBrace"),
              many(seq([
                token_pattern("Ident"),
                opt(seq([
                  keyword_pattern("as"),
                  token_pattern("Ident"),
                ])),
                opt(token_pattern("Comma")),
              ])),
              token_pattern("RBrace"),
            ])),
          ]),
          make_import,
        ),
      ]),
      // Let = "let" ["mut"] Ident [":" Type] "=" Expr
      rule("Let", [
        alt(
          seq([
            keyword_pattern("let"),
            opt(keyword_pattern("mut")),
            token_pattern("Ident"),  // name
            opt(seq([
              token_pattern("Colon"),
              token_pattern("Ident"),  // type annotation
            ])),
            token_pattern("="),
            ref("Expr"),
          ]),
          make_let,
        ),
      ]),
      // Fn = "fn" "(" Ident ")" "(" Ident ":" Type ")" "->" Type "{" Expr "}"
      rule("Fn", [
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
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
    OverloadedFn(_, _, _, _, _, _, span) -> span
    OverloadedApp(_, _, span) -> span
  }
}

/// Parse Tao source code (expression).
pub fn parse(source: String) -> ParseResult(Expr) {
  let error_ast = Int(0, Span("tao", 0, 0, 0, 0))
  grammar_parse(tao_grammar(), source, error_ast)
}

/// Parse Tao module (list of statements).
pub fn parse_module(source: String) -> ParseResult(List(Expr)) {
  // For now, just parse as expression and return as single-item list
  // Full statement parsing will be implemented later
  case parse(source) {
    ParseResultVal(ast: expr, errors: errors) -> ParseResultVal(ast: [expr], errors: errors)
  }
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

/// Helper to create import AST.
fn make_import(values) -> Expr {
  // For now, return a placeholder - imports are handled separately
  // This allows the grammar to parse imports without changing the Expr type
  Int(0, Span("import", 0, 0, 0, 0))
}

/// Helper to create let binding AST.
fn make_let(values) -> Expr {
  // For now, return a placeholder - let bindings are handled in Stmt
  // This allows the grammar to parse let without changing the Expr type
  Int(0, Span("let", 0, 0, 0, 0))
}

/// Format expression to string.
pub fn format_expr(expr: Expr) -> String {
  format_expr_loop(expr, 0)
}

fn format_expr_loop(expr: Expr, parent_prec: Int) -> String {
  case expr {
    Int(n, _) -> int.to_string(n)
    Var(name, _) -> name
    BinOp(l, op, r, _) -> format_binop_op(l, op, r, parent_prec)
    UnaryOp(Not, e, _) -> "!" <> format_expr_loop(e, 100)
    OverloadedFn(name, _type_param, param_name, param_type, _return_type, _body, _) -> {
      "fn (" <> name <> ")(" <> param_name <> ": " <> param_type <> ") -> " <> param_type <> " { ... }"
    }
    OverloadedApp(name, args, _) -> {
      name <> "(" <> string_join(list.map(args, format_expr), ", ") <> ")"
    }
  }
}

fn format_binop_op(left: Expr, op: BinOp, right: Expr, parent_prec: Int) -> String {
  let #(op_str, prec) = case op {
    Add -> #("+", 10)
    Sub -> #("-", 10)
    Mul -> #("*", 20)
    Div -> #("/", 20)
    Eq -> #("==", 5)
    Neq -> #("!=", 5)
    Lt -> #("<", 5)
    Gt -> #(">", 5)
    Lte -> #("<=", 5)
    Gte -> #(">=", 5)
    And -> #("&&", 3)
    Or -> #("||", 3)
  }
  format_binop(left, right, op_str, prec, parent_prec)
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
