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
  type UnaryOperator, OpNot, OpNegate,
  Int as AstInt, String as AstString, type Param as AstParamType, Param as AstParam, TVar,
  BlockStmtExpr, BlockStmtLet, LetDecl, Immutable, Mutable, type BlockStatement,
  Match as AstMatch, MatchClause as AstMatchClause,
  type Pattern as AstPattern, PAny, PVar as AstPVar, PLit as AstPLit, PCtr as AstPCtr,
}
import tao/import_ast.{type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard, type ImportItem, ImportName, ImportType, ImportOperator}
import gleam/int
import gleam/list
import gleam/option.{type Option, Some, None}
import gleam/result
import gleam/string
import syntax/grammar.{
  type Grammar, type ParseResult, type Span, Span, Grammar, type Value, AstValue,
  ParensValue, TokenValue, ListValue, KeywordValue,
  InfixLeft,
  rule, alt, token_pattern, parenthesized, seq, ref, keyword_pattern, many, opt, sep1,
  infix_binary, left_assoc_rule,
  span_from_values, span_from_token, parse as grammar_parse,
  ParseResult as ParseResultVal,
}
import syntax/lexer.{type Token, Token}

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
  /// Arithmetic: -
  OpNeg
}

/// Expression for Tao with overloading support.
pub type Expr {
  /// Integer literal (e.g., 42)
  Int(value: Int, span: Span)
  /// String literal (e.g., "hello")
  Str(value: String, span: Span)
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
  /// Simple function definition (e.g., fn add(x, y) { x + y })
  SimpleFn(
    name: String,
    params: List(#(String, Option(String))),  // (name, type_annotation)
    return_type: Option(String),
    body: Expr,
    span: Span,
  )
  /// Application with potential implicit type args
  OverloadedApp(name: String, args: List(Expr), span: Span)
  /// Regular function application (e.g., add(1, 2))
  App(func: Expr, args: List(Expr), span: Span)
  /// Let binding (e.g., let x = 10)
  Let(name: String, mutable: Bool, type_annotation: Option(String), value: Expr, span: Span)
  /// Block expression (e.g., { let x = 10; x + 1 })
  Block(stmts: List(Expr), span: Span)
  /// Lambda expression (e.g., fn(x, y) { x + y })
  Lambda(type_params: List(String), params: List(#(String, Option(String))), body: Expr, span: Span)
  /// Match expression (e.g., match x { | 0 -> 1 | _ -> x })
  Match(scrutinee: Expr, clauses: List(MatchClause), span: Span)
}

/// A single match clause with pattern, optional guard, and body.
pub type MatchClause {
  MatchClause(pattern: Pattern, guard: Option(Expr), body: Expr, span: Span)
}

/// Pattern for match expressions.
pub type Pattern {
  /// Wildcard: _
  PWild(span: Span)
  /// Variable: x
  PVar(name: String, span: Span)
  /// Literal: 42
  PLit(value: Int, span: Span)
  /// Constructor: Some(x), None
  PCtr(name: String, args: List(Pattern), span: Span)
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
    Str(value, span) -> AstLit(AstString(value), span)
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
    SimpleFn(name, params, _return_type, body, span) -> {
      // Simple functions become Lambda in AST
      // For now, convert first param to lambda param and body to AST
      let ast_body = block_to_ast(body)
      let ast_params = params_to_ast(params, span)
      AstLambda([], ast_params, ast_body, span)
    }
    App(func, args, span) -> {
      let ast_func = expr_to_ast_loop(func)
      let ast_args = list.map(args, expr_to_ast_loop)
      AstCall(ast_func, ast_args, span)
    }
    Lambda(_type_params, params, body, span) -> {
      // Lambda expressions become AstLambda
      let ast_body = case body {
        Block(_, _) -> block_to_ast(body)
        _ -> expr_to_ast_loop(body)
      }
      let ast_params = params_to_ast(params, span)
      AstLambda([], ast_params, ast_body, span)
    }
    Match(scrutinee, clauses, span) -> {
      // Match expression becomes ast.Match
      let ast_scrutinee = expr_to_ast_loop(scrutinee)
      let ast_clauses = list.map(clauses, clause_to_ast)
      AstMatch(ast_scrutinee, ast_clauses, span)
    }
  }
}

fn clause_to_ast(clause: MatchClause) -> ast.MatchClause {
  let MatchClause(pattern, guard, body, span) = clause
  let ast_pattern = pattern_to_ast(pattern)
  let ast_guard = case guard {
    Some(g) -> Some(expr_to_ast_loop(g))
    None -> None
  }
  let ast_body = expr_to_ast_loop(body)
  ast.MatchClause(ast_pattern, ast_guard, ast_body, span)
}

fn pattern_to_ast(pattern: Pattern) -> ast.Pattern {
  case pattern {
    PWild(span) -> PAny(span)
    PVar(name, span) -> AstPVar(name, span)
    PLit(value, span) -> AstPLit(AstInt(value), span)
    PCtr(name, args, span) -> AstPCtr(name, list.map(args, pattern_to_ast), span)
  }
}

fn params_to_ast(params: List(#(String, Option(String))), span: Span) -> List(AstParamType) {
  list.map(params, fn(param) {
    let #(name, type_ann) = param
    let ast_type = case type_ann {
      Some(t) -> Some(TVar(t))
      None -> None
    }
    AstParam(name, ast_type, span)
  })
}

pub fn block_to_ast(block_expr: Expr) -> AstExpr {
  case block_expr {
    Block(stmts, span) -> {
      let ast_stmts = list.map(stmts, expr_to_block_stmt)
      AstBlock(ast_stmts, span)
    }
    _ -> {
      let default_span = Span("error", 0, 0, 0, 0)
      AstBlock([], default_span)
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
    SimpleFn(name, params, return_type, body, span) -> {
      // Function definitions become let bindings with lambdas
      let ast_body = block_to_ast(body)
      let ast_params = params_to_ast(params, span)
      let ast_return_type = case return_type {
        Some(t) -> Some(TVar(t))
        None -> None
      }
      let lambda = AstLambda([], ast_params, ast_body, span)
      BlockStmtLet(LetDecl(name, Immutable, ast_return_type, lambda, span))
    }
    Lambda(_type_params, params, body, span) -> {
      // Lambda expressions in blocks become AstLambda expressions
      let ast_body = case body {
        Block(_, _) -> block_to_ast(body)
        _ -> expr_to_ast_loop(body)
      }
      let ast_params = params_to_ast(params, span)
      let lambda = AstLambda([], ast_params, ast_body, span)
      BlockStmtExpr(lambda)
    }
    _ -> BlockStmtExpr(expr_to_ast_loop(expr))
  }
}

fn unaryop_to_ast(op: UnaryOp) -> UnaryOperator {
  case op {
    Not -> OpNot
    OpNeg -> OpNegate
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

fn make_str(values) -> Expr {
  case values {
    [TokenValue(token)] ->
      Str(token.value, span_from_token(token, "tao"))
    _ -> panic as "Expected string"
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
    SimpleFn(_, _, _, _, span) -> span
    App(_, _, span) -> span
    Lambda(_, _, _, span) -> span
    Match(_, _, span) -> span
    Str(_, span) -> span
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
    tokens: ["Ident", "Number", "String", "LParen", "RParen", "LBrace", "RBrace", "Colon", "Arrow", "Slash", "Star", "Comma", "Equal", "Pipe", "Semi"],
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
      // Program = Stmt* (returned as list, no Block wrapper)
      rule("Program", [
        alt(
          many(seq([
            ref("Stmt"),
            opt(token_pattern("Semi")),  // Optional semicolon separator
          ])),
          fn(values) {
            // many() returns a list of (Stmt, opt(Semi)) pairs
            // Extract statements and ignore semicolons
            let stmts = extract_stmts_with_semicolons(values, [])
            // Return list directly - caller decides how to handle it
            // For single expression, return the expression itself
            // For multiple statements, return as Block
            case stmts {
              [single] -> single
              [] -> Int(0, Span("program", 0, 0, 0, 0))
              _ -> Block(stmts, case list.first(values), list.last(values) {
                Ok(ListValue([first_val])), Ok(ListValue([last_val])) ->
                  case first_val, last_val {
                    AstValue(first_e), AstValue(last_e) ->
                      merge_spans(get_span(first_e), get_span(last_e))
                    _, _ -> Span("program", 0, 0, 0, 0)
                  }
                _, _ -> Span("program", 0, 0, 0, 0)
              })
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
              token_pattern("Ident"),  // type annotation (simple type name)
            ])),
            token_pattern("Equal"),
            opt(ref("Expr")),  // Optional expr for error recovery
          ]),
          fn(values) { make_let(values) },
        ),
      ]),
      // Fn = "fn" name "(" params ")" "{" body "}"  OR  "fn" "(" op ")" "(" param ":" type ")" "->" type "{" body "}"
      rule("Fn", [
        // Simple function: fn name(params) { body }
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("Ident"),  // function name
            token_pattern("LParen"),
            many(seq([
              token_pattern("Ident"),  // param name
              opt(seq([
                token_pattern("Colon"),
                token_pattern("Ident"),  // param type annotation (simple type name)
              ])),
              opt(token_pattern("Comma")),
            ])),
            token_pattern("RParen"),
            opt(seq([
              token_pattern("Arrow"),
              token_pattern("Ident"),  // return type (simple type name)
            ])),
            ref("Block"),  // body
          ]),
          make_simple_fn,
        ),
        // Overloaded function: fn (+)(x: I32) -> I32 { body }
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // operator name
            token_pattern("RParen"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // param name
            token_pattern("Colon"),
            token_pattern("Ident"),  // param type (simple type name)
            token_pattern("RParen"),
            token_pattern("Arrow"),
            token_pattern("Ident"),  // return type (simple type name)
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
        "Logic",
        [
          infix_binary("+", make_add, InfixLeft, 10, " + "),
          infix_binary("-", make_sub, InfixLeft, 10, " - "),
        ],
        10,
      ),
      // Unary operators (prefix)
      rule("Unary", [
        // Prefix negation: -expr
        alt(
          seq([
            keyword_pattern("-"),
            ref("Application"),
          ]),
          fn(values) {
            case values {
              [_, AstValue(expr)] -> UnaryOp(OpNeg, expr, merge_spans(Span("unary", 0, 0, 0, 0), get_span(expr)))
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Prefix logical not: !expr
        alt(
          seq([
            keyword_pattern("!"),
            ref("Application"),
          ]),
          fn(values) {
            case values {
              [_, AstValue(expr)] -> make_not(expr)
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Or just the application
        alt(ref("Application"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      // Application = Primary ("(" Args ")")*
      rule("Application", [
        alt(
          seq([
            ref("Primary"),
            many(seq([
              token_pattern("LParen"),
              many(seq([
                ref("Expr"),
                opt(token_pattern("Comma")),
              ])),
              token_pattern("RParen"),
            ])),
          ]),
          make_app,
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
        // String literal
        alt(
          token_pattern("String"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_str([TokenValue(token)])
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
        // Inline lambda: fn(params) { body } or fn(params) -> Type { body }
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            many(seq([
              token_pattern("Ident"),  // param name
              opt(seq([
                token_pattern("Colon"),
                token_pattern("Ident"),  // type annotation (simple type name)
              ])),
              opt(token_pattern("Comma")),
            ])),
            token_pattern("RParen"),
            opt(seq([
              token_pattern("Arrow"),
              token_pattern("Ident"),  // return type (simple type name)
            ])),
            ref("Block"),  // body
          ]),
          make_inline_lambda,
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
        // Match expression: match scrutinee { | pattern -> body } or match scrutinee -> Type { ... }
        alt(
          seq([
            keyword_pattern("match"),
            ref("Expr"),  // scrutinee
            opt(seq([
              token_pattern("Arrow"),
              token_pattern("Ident"),  // result type annotation (simple type name)
            ])),
            token_pattern("LBrace"),
            many(seq([
              token_pattern("Pipe"),  // |
              ref("Expr"),  // pattern (parsed as expression, converted to pattern)
              opt(seq([
                keyword_pattern("if"),
                ref("Expr"),  // guard
              ])),
              token_pattern("Arrow"),
              ref("Expr"),  // body
            ])),
            token_pattern("RBrace"),
          ]),
          make_match,
        ),
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
    SimpleFn(_, _, _, _, span) -> span
    App(_, _, span) -> span
    Lambda(_, _, _, span) -> span
    Match(_, _, span) -> span
    Str(_, span) -> span
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
  // Parse using the grammar - Program now returns expressions directly
  let error_ast = Int(0, Span("tao", 0, 0, 0, 0))
  let result = grammar_parse(tao_grammar(), source, error_ast)

  // Extract statements - Program returns single expr or Block of multiple
  case result {
    ParseResultVal(ast: expr, errors: errors) -> {
      let stmts = case expr {
        Block(stmts, _) -> stmts
        Int(0, Span("program", _, _, _, _)) -> []  // Empty program
        single -> [single]  // Single expression/statement
      }
      ParseResultVal(ast: stmts, errors: errors)
    }
  }
}

/// Helper to create simple function AST.
fn make_simple_fn(values) -> Expr {
  // Find the function name (second token, first is "fn")
  let name_token = case values {
    [_, TokenValue(t), ..] -> t
    _ -> panic as "Expected function name"
  }

  // Find the body (last AstValue)
  let body_expr = case list.last(values) {
    Ok(AstValue(e)) -> e
    _ -> panic as "Expected function body"
  }

  // Extract params from many result
  // Structure: [fn, name, (, ListValue([Ident, opt([":", Type])]), ...), ), opt([->, Type]), block]
  let params = case values {
    [_, _, _, ListValue(params_many), ..] -> {
      // Each param in params_many is either:
      // - ListValue([TokenValue(name), opt(Comma)]) - no type
      // - ListValue([TokenValue(name), ":", AstValue(type), opt(Comma)]) - with type
      extract_params_from_many_with_types(params_many, [])
    }
    _ -> []
  }

  // Return type is parsed but not used yet (type inference handles it)
  let return_type = None

  let body_span = get_expr_span(body_expr)
  let span = merge_spans(span_from_token(name_token, "tao"), body_span)
  SimpleFn(name_token.value, params, return_type, body_expr, span)
}

/// Helper to create inline lambda AST.
fn make_inline_lambda(values) -> Expr {
  // Find the body (last AstValue)
  let body_expr = case list.last(values) {
    Ok(AstValue(e)) -> e
    _ -> panic as "Expected lambda body"
  }

  // Extract params: [fn, (, ListValue(params), ), opt(Arrow, Type), Block]
  let params = case values {
    [_, _, ListValue(params_many), _, ..] -> {
      extract_params_from_many(params_many, [])
    }
    _ -> []
  }

  let span = case values {
    [KeywordValue(k), ..] -> {
      let Token(_, _, _, _, line, column) = k
      Span("tao", line, column, line, column + 1)
    }
    _ -> Span("error", 0, 0, 0, 0)
  }
  Lambda([], params, body_expr, span)
}

/// Helper to create match expression AST.
fn make_match(values) -> Expr {
  // The structure is: [match_kw, scrut, opt(Arrow, Type), LBrace, ListValue(clauses), ListValue(more), RBrace]
  // or: [match_kw, scrut, LBrace, ListValue(clauses), RBrace]
  // We need to find the RBrace at the end and extract clauses

  // First, find the scrutinee (should be the second element, an AstValue)
  let scrut = case values {
    [_, AstValue(s), ..] -> s
    _ -> panic as "Match: expected scrutinee"
  }

  // Find the match keyword for span
  let match_kw = case values {
    [KeywordValue(kw), ..] -> kw
    _ -> panic as "Match: expected keyword"
  }

  // Extract clauses: try different structures based on optional type annotation
  // With type: [match, scrut, Arrow, Type, LBrace, ListValue, ListValue, RBrace]
  // Without type: [match, scrut, LBrace, ListValue, ListValue, RBrace]
  let clauses = case values {
    [_, _, _, _, TokenValue(lbrace), ListValue(clause_values1), ListValue(clause_values2), _] if lbrace.value == "{" -> {
      list.append(extract_clauses(clause_values1, []), extract_clauses(clause_values2, []))
    }
    [_, _, TokenValue(lbrace), ListValue(clause_values1), ListValue(clause_values2), _] if lbrace.value == "{" -> {
      list.append(extract_clauses(clause_values1, []), extract_clauses(clause_values2, []))
    }
    [_, _, _, _, TokenValue(lbrace), ListValue(clause_values), _] if lbrace.value == "{" -> {
      extract_clauses(clause_values, [])
    }
    [_, _, TokenValue(lbrace), ListValue(clause_values), _] if lbrace.value == "{" -> {
      extract_clauses(clause_values, [])
    }
    _ -> {
      extract_match_clauses(values, [])
    }
  }

  let start_span = Span("tao", match_kw.line, match_kw.column, match_kw.line, match_kw.column + 5)
  let end_span = get_expr_span(scrut)
  let full_span = Span(start_span.file, start_span.start_line, start_span.start_col, end_span.end_line, end_span.end_col)
  Match(scrut, clauses, full_span)
}

fn extract_match_clauses(values: List(Value(Expr)), acc: List(MatchClause)) -> List(MatchClause) {
  case values {
    [] -> list.reverse(acc)
    // No guard: | pattern -> body
    [TokenValue(pipe), AstValue(pattern), TokenValue(arrow), AstValue(body), ..rest] if pipe.value == "|" && arrow.value == "->" -> {
      let p = pattern_ast_to_pattern(pattern)
      let span = get_expr_span(body)
      let clause = MatchClause(p, None, body, span)
      extract_match_clauses(rest, [clause, ..acc])
    }
    // With guard: | pattern if guard -> body
    [TokenValue(pipe), AstValue(pattern), KeywordValue(_if), AstValue(guard), TokenValue(arrow), AstValue(body), ..rest] if pipe.value == "|" && arrow.value == "->" -> {
      let p = pattern_ast_to_pattern(pattern)
      let span = get_expr_span(body)
      let clause = MatchClause(p, Some(guard), body, span)
      extract_match_clauses(rest, [clause, ..acc])
    }
    [_ , ..rest] -> {
      // Skip non-clause tokens (match, scrutinee, braces)
      extract_match_clauses(rest, acc)
    }
  }
}

fn inspect_values(values: List(Value(Expr))) -> String {
  values
  |> list.map(fn(v) {
    case v {
      KeywordValue(t) -> "KeywordValue(" <> t.value <> ")"
      AstValue(_) -> "AstValue(...)"
      ListValue(_) -> "ListValue(...)"
      TokenValue(t) -> "TokenValue(" <> t.value <> ")"
      ParensValue(_) -> "ParensValue(...)"
    }
  })
  |> string.join(", ")
}

fn extract_clauses(clause_values: List(Value(Expr)), acc: List(MatchClause)) -> List(MatchClause) {
  case clause_values {
    [] -> list.reverse(acc)
    // Handle ListValue-wrapped clauses (from many(seq(...)))
    [ListValue(items), ..rest] -> {
      // Recursively extract from the wrapped items
      let sub_clauses = extract_clauses(items, [])
      extract_clauses(rest, list.append(sub_clauses, acc))
    }
    // Handle flat list: | pattern -> body | pattern -> body ...
    [TokenValue(pipe), AstValue(pattern_ast), ..rest_items] if pipe.value == "|" -> {
      let clause_result = extract_single_clause(clause_values, [])
      case clause_result {
        Some(#(pattern, guard, body, remaining)) -> {
          let span = get_expr_span(body)
          let clause = MatchClause(pattern, guard, body, span)
          extract_clauses(remaining, [clause, ..acc])
        }
        None -> extract_clauses(rest_items, acc)
      }
    }
    [_ , ..rest] -> extract_clauses(rest, acc)
  }
}

fn extract_clauses_direct(clause_values: List(Value(Expr)), acc: List(MatchClause)) -> List(MatchClause) {
  // Handle clauses that are direct values (not wrapped in ListValue)
  case clause_values {
    [] -> list.reverse(acc)
    [TokenValue(_pipe), AstValue(pattern_ast), opt_if, TokenValue(_arrow), AstValue(body), ..rest] -> {
      let pattern = pattern_ast_to_pattern(pattern_ast)
      let guard = case opt_if {
        KeywordValue(_) -> {
          case rest {
            [AstValue(g), ..] -> Some(g)
            _ -> None
          }
        }
        _ -> None
      }
      let span = get_expr_span(body)
      let clause = MatchClause(pattern, guard, body, span)
      extract_clauses_direct(rest, [clause, ..acc])
    }
    [_, ..rest] -> extract_clauses_direct(rest, acc)
  }
}

fn extract_single_clause(
  items: List(Value(Expr)),
  acc: List(Value(Expr)),
) -> Option(#(Pattern, Option(Expr), Expr, List(Value(Expr)))) {
  case items {
    [TokenValue(_pipe), AstValue(pattern_ast), ..rest_items] -> {
      let pattern = pattern_ast_to_pattern(pattern_ast)
      extract_clause_guard(rest_items, pattern, acc)
    }
    _ -> None
  }
}

fn extract_clause_guard(
  items: List(Value(Expr)),
  pattern: Pattern,
  acc: List(Value(Expr)),
) -> Option(#(Pattern, Option(Expr), Expr, List(Value(Expr)))) {
  case items {
    [KeywordValue(_if), AstValue(guard_expr), TokenValue(_arrow), AstValue(body), ..rest] -> {
      Some(#(pattern, Some(guard_expr), body, rest))
    }
    [TokenValue(_arrow), AstValue(body), ..rest] -> {
      Some(#(pattern, None, body, rest))
    }
    _ -> None
  }
}

fn pattern_ast_to_pattern(expr: Expr) -> Pattern {
  case expr {
    Var("_", span) -> PWild(span)
    Var(name, span) -> PVar(name, span)
    Int(value, span) -> PLit(value, span)
    // Constructor patterns like Some(x) would need more complex parsing
    // For now, all other expressions become wildcards
    _ -> PWild(Span("error", 0, 0, 0, 0))
  }
}

fn extract_params_from_many(params_many: List(Value(Expr)), acc: List(#(String, Option(String)))) -> List(#(String, Option(String))) {
  case params_many {
    [] -> list.reverse(acc)
    [ListValue([TokenValue(name_tok), _]), ..rest] ->
      extract_params_from_many(rest, [#(name_tok.value, None), ..acc])
    [_, ..rest] -> extract_params_from_many(rest, acc)
  }
}

/// Extract params with type annotations from many result.
/// Each param is: ListValue([TokenValue(name), opt([":", TokenValue(type_name)])])
fn extract_params_from_many_with_types(params_many: List(Value(Expr)), acc: List(#(String, Option(String)))) -> List(#(String, Option(String))) {
  case params_many {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // Each param is [TokenValue(name), opt([":", TokenValue(type_name)])]
      case items {
        [TokenValue(name_tok), TokenValue(_colon), TokenValue(type_tok), ..] ->
          extract_params_from_many_with_types(rest, [#(name_tok.value, Some(type_tok.value)), ..acc])
        [TokenValue(name_tok), ..] ->
          extract_params_from_many_with_types(rest, [#(name_tok.value, None), ..acc])
        _ -> extract_params_from_many_with_types(rest, acc)
      }
    }
    [_, ..rest] -> extract_params_from_many_with_types(rest, acc)
  }
}

fn extract_params(param_list: List(Value(Expr)), acc: List(#(String, Option(String)))) -> List(#(String, Option(String))) {
  case param_list {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // Each param is [TokenValue(name), opt([":", TokenValue(type)])]
      case items {
        [TokenValue(name_tok), TokenValue(_colon), TokenValue(type_tok)] ->
          extract_params(rest, [#(name_tok.value, Some(type_tok.value)), ..acc])
        [TokenValue(name_tok)] ->
          extract_params(rest, [#(name_tok.value, None), ..acc])
        _ -> extract_params(rest, acc)
      }
    }
    // Handle case where params are not wrapped in ListValue
    [TokenValue(name_tok), ..rest] -> {
      // Single token without type annotation
      extract_params(rest, [#(name_tok.value, None), ..acc])
    }
    // Handle case with type annotation but not wrapped
    [TokenValue(name_tok), TokenValue(_colon), TokenValue(type_tok), ..rest] -> {
      extract_params(rest, [#(name_tok.value, Some(type_tok.value)), ..acc])
    }
    [_, ..rest] -> extract_params(rest, acc)
  }
}

/// Helper to create function application AST.
fn make_app(values) -> Expr {
  case values {
    [AstValue(func), ListValue(calls)] -> {
      // Process each call: [LParen, args, RParen]
      // For now, just handle the first call
      case list.first(calls) {
        Ok(ListValue([_, ListValue(args_list), _])) -> {
          // Extract args from the list
          let args = extract_args(args_list, [])
          let span = get_expr_span(func)
          App(func, args, span)
        }
        _ -> func
      }
    }
    [AstValue(func)] -> func
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }
}

fn extract_args(args_list: List(Value(Expr)), acc: List(Expr)) -> List(Expr) {
  case args_list {
    [] -> list.reverse(acc)
    [AstValue(e), ..rest] -> extract_args(rest, [e, ..acc])
    [_, ..rest] -> extract_args(rest, acc)
  }
}

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
  //   ["let", opt("mut"), name, opt([":", Type]), "=", expr]
  // Type returns a String (the type name)
  // So we get either:
  //   With mut and type: ["let", "mut", name, ":", type_string, "=", expr] (7 values)
  //   With mut only:     ["let", "mut", name, "=", expr] (5 values)
  //   With type only:    ["let", name, ":", type_string, "=", expr] (6 values)
  //   Neither:           ["let", name, "=", expr] (4 values)

  // Check for "mut" keyword (second element, as KeywordValue)
  let mutable = case list.first(list.drop(values, 1)) {
    Ok(KeywordValue(token)) if token.value == "mut" -> True
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
        Ok(TokenValue(t)) -> Some(t.value)  // Simple type name
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

/// Extract statements from values that may include semicolons.
/// Values are ListValue containing [Stmt, opt(Semicolon)]
fn extract_stmts_with_semicolons(values: List(Value(Expr)), acc: List(Expr)) -> List(Expr) {
  case values {
    [] -> list.reverse(acc)
    [ListValue(stmt_semi_list), ..rest] -> {
      // stmt_semi_list contains [Stmt, opt(Semicolon)]
      // Extract the statement (first element that's an AstValue)
      case extract_first_ast_value(stmt_semi_list, None) {
        Some(e) -> extract_stmts_with_semicolons(rest, [e, ..acc])
        None -> extract_stmts_with_semicolons(rest, acc)
      }
    }
    [_, ..rest] -> extract_stmts_with_semicolons(rest, acc)
  }
}

/// Helper to extract the first AstValue from a list.
fn extract_first_ast_value(values: List(Value(Expr)), found: Option(Expr)) -> Option(Expr) {
  case values {
    [] -> found
    [AstValue(e), ..] -> Some(e)
    [ListValue([AstValue(e)]), ..] -> Some(e)
    [_, ..rest] -> extract_first_ast_value(rest, found)
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
    Str(s, _) -> "\"" <> s <> "\""
    Var(name, _) -> name
    BinOp(l, op, r, _) -> format_binop_op(l, op, r, parent_prec)
    UnaryOp(Not, e, _) -> "!" <> format_expr_loop(e, 100)
    UnaryOp(OpNeg, e, _) -> "-" <> format_expr_loop(e, 100)
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
    SimpleFn(name, params, return_type, _body, _) -> {
      let params_str = string_join(
        list.map(params, fn(p) {
          let #(pname, ptype) = p
          pname <> case ptype {
            Some(t) -> ": " <> t
            None -> ""
          }
        }),
        ", ",
      )
      let ret_str = case return_type {
        Some(t) -> " -> " <> t
        None -> ""
      }
      "fn " <> name <> "(" <> params_str <> ")" <> ret_str <> " { ... }"
    }
    App(func, args, _) -> {
      format_expr(func) <> "(" <> string_join(list.map(args, format_expr), ", ") <> ")"
    }
    Lambda(_type_params, params, _body, _) -> {
      let params_str = string_join(
        list.map(params, fn(p) {
          let #(pname, ptype) = p
          pname <> case ptype {
            Some(t) -> ": " <> t
            None -> ""
          }
        }),
        ", ",
      )
      "fn(" <> params_str <> ") { ... }"
    }
    Match(scrutinee, clauses, _) -> {
      let clauses_str = string_join(
        list.map(clauses, fn(clause) {
          let MatchClause(pattern, guard, body, _) = clause
          let pattern_str = format_pattern(pattern)
          let guard_str = case guard {
            Some(g) -> " if " <> format_expr(g)
            None -> ""
          }
          "| " <> pattern_str <> guard_str <> " -> " <> format_expr(body)
        }),
        " ",
      )
      "match " <> format_expr(scrutinee) <> " { " <> clauses_str <> " }"
    }
  }
}

fn format_pattern(pattern: Pattern) -> String {
  case pattern {
    PWild(_) -> "_"
    PVar(name, _) -> name
    PLit(value, _) -> int.to_string(value)
    PCtr(name, args, _) -> {
      case args {
        [] -> name
        _ -> name <> "(" <> string_join(list.map(args, format_pattern), ", ") <> ")"
      }
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
