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
import tao/ast.{
  type Expr as AstExpr, Var as AstVar, Lit as AstLit, BinOp as AstBinOpExpr,
  UnaryOp as AstUnaryOp, Lambda as AstLambda, Call as AstCall, Block as AstBlock,
  type BinOperator, OpAdd, OpSub, OpMul, OpDiv, OpEq, OpNeq, OpLt, OpGt, OpLte, OpGte, OpAnd, OpOr,
  type UnaryOperator, OpNot,
  Int as AstInt, type Param as AstParamType, Param as AstParam, TVar,
  BlockStmtExpr, BlockStmtLet, LetDecl, Immutable, Mutable, type BlockStatement,
}
import tao/import_ast.{type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard, type ImportItem, ImportName, ImportType, ImportOperator}
import gleam/int
import gleam/list
import gleam/option.{type Option, Some, None}
import gleam/result
import gleam/string
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
  /// Let binding (e.g., let x = 10)
  Let(name: String, mutable: Bool, type_annotation: Option(String), value: Expr, span: Span)
  /// Block expression (e.g., { let x = 10; x + 1 })
  Block(stmts: List(Expr), span: Span)
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
    Let(name, _mutable, _type_annotation, _value, span) -> {
      // Let bindings are handled at the statement level, not expression level
      // This case should not be reached for top-level lets
      AstVar(name, span)
    }
    Block(stmts, span) -> {
      // Convert block statements to AST
      // Let expressions become BlockStmtLet, others become BlockStmtExpr
      let ast_stmts = list.map(stmts, expr_to_block_stmt)
      AstBlock(ast_stmts, span)
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

fn expr_to_block_stmt(expr: Expr) -> BlockStatement {
  case expr {
    Let(name, mutable, type_annotation, value, span) -> {
      let mutability = case mutable {
        True -> Mutable
        False -> Immutable
      }
      let ast_type = case type_annotation {
        Some(t) -> Some(TVar(t))
        None -> None
      }
      BlockStmtLet(LetDecl(name, mutability, ast_type, expr_to_ast_loop(value), span))
    }
    _ -> BlockStmtExpr(expr_to_ast_loop(expr))
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
    Let(_, _, _, _, span) -> span
    Block(_, span) -> span
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
    tokens: ["Ident", "Number", "LParen", "RParen", "LBrace", "RBrace", "Colon", "Arrow", "Slash", "Star", "Comma", "Equal"],
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
      // Program = Stmt* (wrapped in a block)
      rule("Program", [
        alt(
          many(ref("Stmt")),
          fn(values) {
            // many() returns a list of wrapped statements
            // Extract all statements and wrap in a block
            let stmts = extract_stmts(values, [])
            let span = case list.first(values), list.last(values) {
              Ok(ListValue([first_val])), Ok(ListValue([last_val])) ->
                case first_val, last_val {
                  AstValue(first_e), AstValue(last_e) ->
                    merge_spans(get_span(first_e), get_span(last_e))
                  _, _ -> Span("program", 0, 0, 0, 0)
                }
              _, _ -> Span("program", 0, 0, 0, 0)
            }
            Block(stmts, span)
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
            token_pattern("Equal"),
            ref("Expr"),
          ]),
          fn(values) { make_let(values) },
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
        // Variable reference
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
        // Block: { stmts }
        alt(ref("Block"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      // Block = "{" Stmt* "}"
      rule("Block", [
        alt(
          seq([
            token_pattern("LBrace"),
            many(ref("Stmt")),
            token_pattern("RBrace"),
          ]),
          make_block,
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
    Let(_, _, _, _, span) -> span
    Block(_, span) -> span
  }
}

/// Parse Tao source code (expression).
pub fn parse(source: String) -> ParseResult(Expr) {
  let error_ast = Int(0, Span("tao", 0, 0, 0, 0))
  grammar_parse(tao_grammar(), source, error_ast)
}

/// Parse Tao module (list of statements).
/// Returns all statements parsed from the source.
pub fn parse_module(source: String) -> ParseResult(List(Expr)) {
  // Parse using the grammar - the Program rule returns a Block with all statements
  let error_ast = Int(0, Span("tao", 0, 0, 0, 0))
  let result = grammar_parse(tao_grammar(), source, error_ast)

  // Extract statements from the Block
  case result {
    ParseResultVal(ast: expr, errors: errors) -> {
      let stmts = case expr {
        Block(stmts, _) -> stmts
        _ -> [expr]
      }
      ParseResultVal(ast: stmts, errors: errors)
    }
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
  // The grammar sequence is:
  //   ["let", opt("mut"), name, opt([":", type]), "=", expr]
  // opt() includes/excludes values (no Option wrapper)
  // So we get either:
  //   With mut and type: ["let", "mut", name, ":", type, "=", expr] (7 values)
  //   With mut only:     ["let", "mut", name, "=", expr] (5 values)
  //   With type only:    ["let", name, ":", type, "=", expr] (6 values)
  //   Neither:           ["let", name, "=", expr] (4 values)

  // Check for "mut" keyword
  let mutable = case list.first(list.drop(values, 1)) {
    Ok(TokenValue(token)) if token.value == "mut" -> True
    _ -> False
  }

  // Find the name (first TokenValue after "let" and optional "mut")
  let start_idx = case mutable {
    True -> 2
    False -> 1
  }
  let name_and_rest = find_name(list.drop(values, start_idx))
  let #(name, rest_after_name) = name_and_rest

  // Check if next is ":" (has type) or "=" (no type)
  let #(type_annotation, after_eq) = case list.first(rest_after_name) {
    Ok(TokenValue(token)) if token.value == ":" -> {
      // Has type: skip ":" and type token, then skip "="
      let without_colon = list.drop(rest_after_name, 1)
      let type_tok = case list.first(without_colon) {
        Ok(TokenValue(t)) -> Some(t.value)
        _ -> None
      }
      let without_type = list.drop(without_colon, 1)
      let without_eq = list.drop(without_type, 1)
      #(type_tok, without_eq)
    }
    _ -> {
      // No type, next should be "="
      #(None, list.drop(rest_after_name, 1))
    }
  }

  // Next should be the expression
  let value_expr = case list.first(after_eq) {
    Ok(AstValue(e)) -> e
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }

  Let(name, mutable, type_annotation, value_expr, Span("let", 0, 0, 0, 0))
}

fn make_block(values) -> Expr {
  // values = [LBrace, stmts (ListValue), RBrace]
  // stmts is a list of ListValue(AstValue(expr))
  case values {
    [_, ListValue(stmt_values), _] -> {
      // Extract expressions from the wrapped values
      let stmts = extract_stmts(stmt_values, [])
      let span = case list.first(values), list.last(values) {
        Ok(TokenValue(start)), Ok(TokenValue(end)) ->
          Span("tao", start.start, start.line, start.column, end.end)
        _, _ -> Span("block", 0, 0, 0, 0)
      }
      Block(stmts, span)
    }
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }
}

fn extract_stmts(values: List(Value(Expr)), acc: List(Expr)) -> List(Expr) {
  case values {
    [] -> list.reverse(acc)
    [ListValue([AstValue(e)]), ..rest] -> extract_stmts(rest, [e, ..acc])
    [AstValue(e), ..rest] -> extract_stmts(rest, [e, ..acc])
    [_, ..rest] -> extract_stmts(rest, acc)
  }
}

/// Find the name token in a let binding.
fn find_name(values: List(Value(Expr))) -> #(String, List(Value(Expr))) {
  case values {
    [] -> #("error", [])
    [TokenValue(t), ..rest] -> #(t.value, rest)
    [_, ..rest] -> find_name(rest)  // Skip mut or other tokens
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
    BinOp(l, op, r, _) -> format_binop_op(l, op, r, parent_prec)
    UnaryOp(Not, e, _) -> "!" <> format_expr_loop(e, 100)
    OverloadedFn(name, _type_param, param_name, param_type, _return_type, _body, _) -> {
      "fn (" <> name <> ")(" <> param_name <> ": " <> param_type <> ") -> " <> param_type <> " { ... }"
    }
    OverloadedApp(name, args, _) -> {
      name <> "(" <> string_join(list.map(args, format_expr), ", ") <> ")"
    }
    Let(name, mutable, type_annotation, value, _) -> {
      let mut_str = case mutable {
        True -> "mut "
        False -> ""
      }
      let type_str = case type_annotation {
        Some(t) -> ": " <> t
        None -> ""
      }
      "let " <> mut_str <> name <> type_str <> " = " <> format_expr(value)
    }
    Block(stmts, _) -> {
      "{ " <> string_join(list.map(stmts, format_expr), "; ") <> " }"
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
