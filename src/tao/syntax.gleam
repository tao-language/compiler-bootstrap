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
  Int as AstInt, Float as AstFloat, String as AstString, type Param, Param as AstParam, TVar,
  BlockStmtExpr, BlockStmtLet, LetDecl, Immutable, Mutable, type BlockStatement,
  Match as AstMatch, MatchClause as AstMatchClause, If as AstIf,
  type Pattern as AstPattern, PAny, PVar as AstPVar, PLit as AstPLit, PCtr as AstPCtr,
  type Type as AstType, TFn, TApp, TRecord, TTuple, THole,
}
import tao/import_ast.{type Import, ImportModule, ImportAlias, ImportSelective, ImportSelectiveAlias, ImportWildcard, type ImportItem, ImportName, ImportType, ImportOperator}
import gleam/int
import gleam/float
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
  /// Float literal (e.g., 3.14)
  Float(value: Float, span: Span)
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
  /// If expression (e.g., if cond { then } else { else })
  If(condition: Expr, then_branch: Expr, else_branch: Option(Expr), span: Span)
  /// For loop (e.g., for x in xs { ... })
  For(pattern: Pattern, collection: Expr, body: List(Expr), span: Span)
  /// While loop (e.g., while cond { ... })
  While(condition: Expr, body: List(Expr), span: Span)
  /// Infinite loop (e.g., loop { ... })
  Loop(body: List(Expr), span: Span)
  /// Break statement
  Break(span: Span)
  /// Continue statement
  Continue(span: Span)
  /// Test statement (e.g., test "name" { expr })
  Test(name: String, body: Expr, span: Span)
  /// Run statement (e.g., run expr)
  Run(value: Expr, span: Span)
  /// Import statement (e.g., import prelude/bool.{True, False})
  Import(import_item: Import, span: Span)
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
    Float(value, span) -> AstLit(AstFloat(value), span)
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
    If(cond, then_expr, else_expr, span) -> {
      // If expression becomes ast.If
      let ast_cond = expr_to_ast_loop(cond)
      let ast_then = expr_to_ast_loop(then_expr)
      let ast_else = case else_expr {
        Some(e) -> Some(expr_to_ast_loop(e))
        None -> None
      }
      AstIf(ast_cond, ast_then, ast_else, span)
    }
    Test(name, body, span) -> {
      // Test statements become a block with the test body
      // The test name is stored in a comment or metadata (for now, just the body)
      let ast_body = expr_to_ast_loop(body)
      // For now, tests are just the body expression
      // A proper implementation would wrap in a test harness
      ast_body
    }
    Run(value, span) -> {
      // Run statements just evaluate the value
      expr_to_ast_loop(value)
    }
    For(pattern, collection, body, span) -> {
      // For loop becomes a fold/map in AST
      let ast_collection = expr_to_ast_loop(collection)
      let ast_body = block_to_ast(Block(body, span))
      // Placeholder: for now just return the collection
      // Full implementation would create a fold expression
      ast_collection
    }
    While(condition, body, span) -> {
      // While loop becomes a fixpoint in AST
      let ast_condition = expr_to_ast_loop(condition)
      let ast_body = block_to_ast(Block(body, span))
      // Placeholder: for now just return the condition
      // Full implementation would create a fixpoint expression
      ast_condition
    }
    Loop(body, span) -> {
      // Loop becomes a fixpoint in AST
      let ast_body = block_to_ast(Block(body, span))
      // Placeholder: for now return unit
      // Full implementation would create a fixpoint expression
      AstBlock([], span)
    }
    Break(span) -> {
      // Break becomes a return of unit
      AstBlock([], span)
    }
    Continue(span) -> {
      // Continue becomes a return of unit
      AstBlock([], span)
    }
    Import(_, span) -> {
      // Imports are handled at the statement level
      // Return a placeholder
      AstBlock([], span)
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

pub fn pattern_to_ast(pattern: Pattern) -> ast.Pattern {
  case pattern {
    PWild(span) -> PAny(span)
    PVar(name, span) -> AstPVar(name, span)
    PLit(value, span) -> AstPLit(AstInt(value), span)
    PCtr(name, args, span) -> AstPCtr(name, list.map(args, pattern_to_ast), span)
  }
}

fn params_to_ast(params: List(#(String, Option(String))), span: Span) -> List(Param) {
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
    If(_, _, _, _) -> {
      // If expressions are kept as-is
      expr_to_ast_loop(block_expr)
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
    If(_, _, _, _) -> {
      // If expressions are kept as-is
      BlockStmtExpr(expr_to_ast_loop(expr))
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

fn param(name: String, type_: String, span: Span) -> Param {
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

fn make_float(values) -> Expr {
  case values {
    [TokenValue(token)] ->
      Float(
        float.parse(token.value) |> result.unwrap(0.0),
        span_from_token(token, "tao"),
      )
    _ -> panic as "Expected float"
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
    Float(_, span) -> span
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
    If(_, _, _, span) -> span
    For(_, _, _, span) -> span
    While(_, _, span) -> span
    Loop(_, span) -> span
    Break(span) -> span
    Continue(span) -> span
    Str(_, span) -> span
    Test(_, _, span) -> span
    Run(_, span) -> span
    Import(_, span) -> span
  }
}

/// Convert block to test body expression (last statement or block itself).
fn block_to_test_body(block: Expr) -> Expr {
  case block {
    Block(stmts, span) -> {
      case list.last(stmts) {
        Ok(last) -> last
        Error(_) -> Int(0, span)
      }
    }
    _ -> block
  }
}

/// Convert block to expression (for if/else branches).
fn block_to_expr(block: Expr) -> Expr {
  case block {
    Block(stmts, span) -> {
      case list.last(stmts) {
        Ok(last) -> last
        Error(_) -> Block([], span)
      }
    }
    _ -> block
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
    keywords: ["fn", "let", "mut", "match", "if", "else", "type", "import", "export", "as", "comptime", "true", "false", "for", "in", "while", "loop", "break", "continue", "return", "yield", "test", "run"],
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
      // Stmt = Import | Fn | Let | Test | Run | For | While | Loop | Break | Continue | Return | Yield | Expr
      rule("Stmt", [
        // Import statement
        alt(ref("Import"), fn(values) {
          case values {
            [AstValue(e)] -> e
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
        // Test statement: test "name" { expr }
        alt(ref("Test"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Run statement: run expr
        alt(ref("Run"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // For loop: for pattern in collection { body... }
        alt(ref("For"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // While loop: while condition { body... }
        alt(ref("While"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Loop: loop { body... }
        alt(ref("Loop"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
        // Break statement
        alt(
          keyword_pattern("break"),
          fn(values) {
            case values {
              [KeywordValue(kw)] -> {
                let span = Span("tao", kw.line, kw.column, kw.line, kw.column + 5)
                Break(span)
              }
              _ -> Break(Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Continue statement
        alt(
          keyword_pattern("continue"),
          fn(values) {
            case values {
              [KeywordValue(kw)] -> {
                let span = Span("tao", kw.line, kw.column, kw.line, kw.column + 8)
                Continue(span)
              }
              _ -> Continue(Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Expression statement
        alt(ref("Expr"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("empty", 0, 0, 0, 0))
          }
        }),
      ]),
      // Import statement: import path [as alias] [.{name1, name2, ...}]
      rule("Import", [
        alt(
          seq([
            keyword_pattern("import"),
            token_pattern("Ident"),  // path component
            many(seq([
              token_pattern("Operator"),  // / slash
              token_pattern("Ident"),  // path component
            ])),
            opt(seq([
              keyword_pattern("as"),
              token_pattern("Ident"),  // alias
            ])),
            opt(seq([
              token_pattern("Dot"),  // . dot for selective import
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
      // Type = Ident | "fn" "(" [Type ("," Type)*] ")" "->" Type | Ident "(" [Type ("," Type)*] ")"
      rule("Type", [
        // Function type: fn(I32, I32) -> I32 - most specific, check first
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            opt(seq([
              ref("Type"),
              many(seq([
                token_pattern("Comma"),
                ref("Type"),
              ])),
            ])),
            token_pattern("RParen"),
            token_pattern("Arrow"),
            ref("Type"),
          ]),
          fn(values) { Var("fn_type", Span("type", 0, 0, 0, 0)) },  // Dummy expr
        ),
        // Generic type: List(Int) - check before simple type
        alt(
          seq([
            token_pattern("Ident"),
            seq([
              token_pattern("LParen"),
              sep1(ref("Type"), token_pattern("Comma")),
              token_pattern("RParen"),
            ]),
          ]),
          fn(values) {
            // Extract the type name from the first token
            case values {
              [TokenValue(t), ..] -> Var(t.value, Span(t.kind, t.line, t.column, t.line, t.column))
              _ -> Var("generic_type", Span("type", 0, 0, 0, 0))
            }
          },
        ),
        // Simple type: I32, String, etc. - check last (least specific)
        alt(
          token_pattern("Ident"),
          fn(v) {
            case v {
              [TokenValue(t)] -> Var(t.value, Span(t.kind, t.line, t.column, t.line, t.column))
              _ -> Var("Unknown", Span("unknown", 0, 0, 0, 0))
            }
          },
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
              ref("Type"),  // type annotation
            ])),
            token_pattern("Equal"),
            opt(ref("Expr")),  // Optional expr for error recovery
          ]),
          fn(values) { make_let(values) },
        ),
      ]),
      // Test = "test" String "{" Expr "}"
      rule("Test", [
        alt(
          seq([
            keyword_pattern("test"),
            token_pattern("String"),  // test name
            ref("Block"),  // test body
          ]),
          fn(values) {
            case values {
              [_, TokenValue(name_token), AstValue(body_expr)] -> {
                // Extract string content (remove quotes)
                let name = string.slice(name_token.value, 1, string.length(name_token.value) - 2)
                let span = span_from_token(name_token, "tao")
                Test(name, block_to_test_body(body_expr), span)
              }
              _ -> Int(0, Span("empty", 0, 0, 0, 0))
            }
          },
        ),
      ]),
      // Run = "run" Expr
      rule("Run", [
        alt(
          seq([
            keyword_pattern("run"),
            ref("Expr"),
          ]),
          fn(values) {
            case values {
              [_, AstValue(e)] -> {
                let span = get_expr_span(e)
                Run(e, span)
              }
              _ -> Int(0, Span("empty", 0, 0, 0, 0))
            }
          },
        ),
      ]),
      // For = "for" Pattern "in" Expr Block
      rule("For", [
        alt(
          seq([
            keyword_pattern("for"),
            ref("Expr"),  // pattern (parsed as expr, converted to pattern)
            keyword_pattern("in"),
            ref("Expr"),  // collection
            ref("Block"),  // body
          ]),
          make_for,
        ),
      ]),
      // While = "while" Expr Block
      rule("While", [
        alt(
          seq([
            keyword_pattern("while"),
            ref("Expr"),  // condition
            ref("Block"),  // body
          ]),
          make_while,
        ),
      ]),
      // Loop = "loop" Block
      rule("Loop", [
        alt(
          seq([
            keyword_pattern("loop"),
            ref("Block"),  // body
          ]),
          make_loop,
        ),
      ]),
      // Fn = "fn" name "(" params ")" "{" body "}"  OR  "fn" "(" op ")" "(" param ":" type ")" "->" type "{" body "}"
      rule("Fn", [
        // Overloaded function with Ident name: fn (add)(x: I32) -> I32 { body }
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // operator name
            token_pattern("RParen"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // param name
            token_pattern("Colon"),
            ref("Type"),  // param type
            token_pattern("RParen"),
            token_pattern("Arrow"),
            ref("Type"),  // return type
            ref("Block"),  // body
          ]),
          make_overloaded_fn,
        ),
        // Overloaded function with Operator name: fn (+)(x: I32) -> I32 { body }
        alt(
          seq([
            keyword_pattern("fn"),
            token_pattern("LParen"),
            token_pattern("Operator"),  // operator name
            token_pattern("RParen"),
            token_pattern("LParen"),
            token_pattern("Ident"),  // param name
            token_pattern("Colon"),
            ref("Type"),  // param type
            token_pattern("RParen"),
            token_pattern("Arrow"),
            ref("Type"),  // return type
            ref("Block"),  // body
          ]),
          make_overloaded_fn,
        ),
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
                ref("Type"),  // param type annotation
              ])),
              opt(token_pattern("Comma")),
            ])),
            token_pattern("RParen"),
            opt(seq([
              token_pattern("Arrow"),
              ref("Type"),  // return type
            ])),
            ref("Block"),  // body
          ]),
          make_simple_fn,
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
      // Expr = Unary (top-level expression)
      rule("Expr", [
        alt(ref("Unary"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      // Unary operators (prefix) - right associative for chaining
      rule("Unary", [
        // Prefix negation: -expr (can chain: --x)
        alt(
          seq([
            keyword_pattern("-"),
            ref("Unary"),  // Reference Unary for chaining
          ]),
          fn(values) {
            case values {
              [_, AstValue(expr)] -> UnaryOp(OpNeg, expr, merge_spans(Span("unary", 0, 0, 0, 0), get_span(expr)))
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Prefix logical not: !expr (can chain: !!x)
        alt(
          seq([
            keyword_pattern("!"),
            ref("Unary"),  // Reference Unary for chaining
          ]),
          fn(values) {
            case values {
              [_, AstValue(expr)] -> make_not(expr)
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Or just the application (base case)
        alt(ref("Application"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      // Application = Atom ("(" Args ")")*
      // Atom = Primary | "(" Expr ")"
      // This allows nested applications like f(g(x))
      rule("Application", [
        alt(
          seq([
            ref("Atom"),
            many(seq([
              token_pattern("LParen"),
              sep1(ref("Expr"), token_pattern("Comma")),
              token_pattern("RParen"),
            ])),
          ]),
          make_app,
        ),
        alt(ref("Atom"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      // Atom = Primary | "(" Expr ")"
      rule("Atom", [
        // Parenthesized expression
        alt(
          parenthesized("Expr"),
          fn(values) {
            case values {
              [ParensValue([AstValue(expr)])] -> expr
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Primary (fallback)
        alt(ref("Primary"), fn(values) {
          case values {
            [AstValue(e)] -> e
            _ -> Int(0, Span("error", 0, 0, 0, 0))
          }
        }),
      ]),
      rule("Primary", [
        // Integer literal
        alt(
          token_pattern("Number"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_int([TokenValue(token)])
              _ -> Int(0, Span("error", 0, 0, 0, 0))
            }
          },
        ),
        // Float literal
        alt(
          token_pattern("Float"),
          fn(values) {
            case values {
              [TokenValue(token)] -> make_float([TokenValue(token)])
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
        // If expression: if cond { then } else { else }
        alt(
          seq([
            keyword_pattern("if"),
            ref("Expr"),  // condition
            ref("Block"),  // then branch
            keyword_pattern("else"),
            ref("Block"),  // else branch
          ]),
          make_if,
        ),
        // For loop: for pattern in collection { body... }
        alt(
          seq([
            keyword_pattern("for"),
            ref("Expr"),  // pattern (parsed as expression, converted to pattern)
            keyword_pattern("in"),
            ref("Expr"),  // collection
            ref("Block"),  // body
          ]),
          make_for,
        ),
        // While loop: while condition { body... }
        alt(
          seq([
            keyword_pattern("while"),
            ref("Expr"),  // condition
            ref("Block"),  // body
          ]),
          make_while,
        ),
        // Loop: loop { body... }
        alt(
          seq([
            keyword_pattern("loop"),
            ref("Block"),  // body
          ]),
          make_loop,
        ),
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
    Float(_, span) -> span
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
    If(_, _, _, span) -> span
    For(_, _, _, span) -> span
    While(_, _, span) -> span
    Loop(_, span) -> span
    Break(span) -> span
    Continue(span) -> span
    Str(_, span) -> span
    Test(_, _, span) -> span
    Run(_, span) -> span
    Import(_, span) -> span
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

  // Extract params from values - params are ListValue items between ( and )
  let params = extract_fn_params(values, [])

  // Return type - extract from opt([Arrow, TokenValue(type_string)])
  // The structure varies based on whether params and return type are present
  let return_type = extract_return_type_from_values(values)

  let body_span = get_expr_span(body_expr)
  let span = merge_spans(span_from_token(name_token, "tao"), body_span)
  SimpleFn(name_token.value, params, return_type, body_expr, span)
}

/// Extract return type from function values.
fn extract_return_type_from_values(values: List(Value(Expr))) -> Option(String) {
  case find_arrow_and_return_type(values, False) {
    Some(type_values) -> Some(reconstruct_type_string(type_values))
    None -> None
  }
}

fn find_arrow_and_return_type(values: List(Value(Expr)), found_arrow: Bool) -> Option(List(Value(Expr))) {
  case values {
    [] -> None
    [TokenValue(t), ..rest] -> {
      case t.value == "->" {
        True -> Some(rest)  // Return everything after "->"
        False -> find_arrow_and_return_type(rest, False)
      }
    }
    [_, ..rest] -> find_arrow_and_return_type(rest, False)
  }
}

/// Helper to create inline lambda AST.
fn make_inline_lambda(values) -> Expr {
  // Find the body (last AstValue)
  let body_expr = case list.last(values) {
    Ok(AstValue(e)) -> e
    _ -> panic as "Expected lambda body"
  }

  // Extract params from the values
  // Structure: [KeywordValue(fn), TokenValue(LParen), ListValue(param1), ListValue(param2), ..., TokenValue(RParen), opt(Arrow, Type), AstValue(Block)]
  let params = extract_lambda_params(values, [])

  let span = case values {
    [KeywordValue(k), ..] -> {
      let Token(_, _, _, _, line, column) = k
      Span("tao", line, column, line, column + 1)
    }
    _ -> Span("error", 0, 0, 0, 0)
  }
  Lambda([], params, body_expr, span)
}

fn extract_fn_params(
  values: List(Value(Expr)),
  acc: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case values {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // This is a param - extract it
      let param = extract_single_fn_param(items)
      case param {
        Some(p) -> extract_fn_params(rest, [p, ..acc])
        None -> extract_fn_params(rest, acc)
      }
    }
    [_, ..rest] -> {
      // Skip non-param values
      extract_fn_params(rest, acc)
    }
  }
}

fn extract_single_fn_param(items: List(Value(Expr))) -> Option(#(String, Option(String))) {
  case items {
    [TokenValue(name_tok), TokenValue(_colon), ..type_values] -> {
      let type_str = reconstruct_type_string(type_values)
      Some(#(name_tok.value, Some(type_str)))
    }
    [TokenValue(name_tok), ..] -> {
      Some(#(name_tok.value, None))
    }
    _ -> None
  }
}

fn extract_lambda_params(
  values: List(Value(Expr)),
  acc: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case values {
    [] -> list.reverse(acc)
    // Handle nested list from many(seq(...))
    [ListValue(nested_list), ..rest] -> {
      // Extract all params from the nested list
      let params = extract_params_from_nested_list(nested_list, [])
      extract_lambda_params(rest, list.append(params, acc))
    }
    // Handle the case where params are in a nested list (from many(seq(...)))
    [AstValue(_), ..rest] -> {
      // Skip AstValue (body, blocks, etc.)
      extract_lambda_params(rest, acc)
    }
    [_, ..rest] -> {
      // Skip non-param values (fn keyword, parens, etc.)
      extract_lambda_params(rest, acc)
    }
  }
}

fn extract_params_from_nested_list(
  nested_list: List(Value(Expr)),
  acc: List(#(String, Option(String))),
) -> List(#(String, Option(String))) {
  case nested_list {
    [] -> acc
    // Handle grouped param items (from seq(...))
    // Each group is: [TokenValue(name), opt_type_ann, opt_comma]
    // We need to process groups, not individual items
    [TokenValue(name_tok), opt_type_ann, opt_comma, ..rest] -> {
      // Extract type annotation from opt_type_ann
      let type_ann = case opt_type_ann {
        ListValue(type_items) -> extract_type_from_inner(type_items)
        _ -> None
      }
      // Skip comma if present
      let remaining = case opt_comma {
        TokenValue(t) if t.value == "," -> rest
        _ -> nested_list |> list.drop(1) |> list.drop(1) |> list.drop(1)
      }
      extract_params_from_nested_list(remaining, [ #(name_tok.value, type_ann), ..acc])
    }
    // Handle single param without type annotation or comma
    [TokenValue(name_tok), ..rest] -> {
      extract_params_from_nested_list(rest, [ #(name_tok.value, None), ..acc])
    }
    [ListValue(items), ..rest] -> {
      // This is a param wrapped in ListValue - extract it
      let param = extract_single_param_with_span(items, nested_list)
      case param {
        Some(p) -> extract_params_from_nested_list(rest, [p, ..acc])
        None -> extract_params_from_nested_list(rest, acc)
      }
    }
    [_, ..rest] -> {
      // Skip non-param values
      extract_params_from_nested_list(rest, acc)
    }
  }
}

fn extract_type_and_skip_comma(items: List(Value(Expr))) -> #(Option(String), List(Value(Expr))) {
  case items {
    // Type annotation (wrapped in ListValue from seq) followed by comma
    [ListValue(type_items), TokenValue(comma_tok), ..rest] if comma_tok.value == "," -> {
      #(extract_type_from_inner(type_items), rest)
    }
    // Type annotation (wrapped in ListValue from seq) without comma
    [ListValue(type_items), ..rest] -> {
      #(extract_type_from_inner(type_items), rest)
    }
    // Comma without type annotation (shouldn't happen, but handle it)
    [TokenValue(comma_tok), ..rest] if comma_tok.value == "," -> {
      #(None, rest)
    }
    // No type annotation, no comma - return items as remaining
    _ -> {
      #(None, items)
    }
  }
}

fn extract_type_from_inner(inner_list: List(Value(Expr))) -> Option(String) {
  case inner_list {
    [TokenValue(_colon), TokenValue(type_tok), ..] -> Some(type_tok.value)
    [TokenValue(type_tok), ..] -> Some(type_tok.value)
    [_, ..rest] -> extract_type_from_inner(rest)
    [] -> None
  }
}

fn extract_params_from_many_with_spans(
  params_many: List(Value(Expr)),
  acc: List(#(String, Option(String))),
  all_values: List(Value(Expr)),
) -> List(#(String, Option(String))) {
  case params_many {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      let param = extract_single_param_with_span(items, all_values)
      case param {
        Some(p) -> extract_params_from_many_with_spans(rest, [p, ..acc], all_values)
        None -> extract_params_from_many_with_spans(rest, acc, all_values)
      }
    }
    [_, ..rest] -> extract_params_from_many_with_spans(rest, acc, all_values)
  }
}

fn extract_single_param_with_span(
  items: List(Value(Expr)),
  all_values: List(Value(Expr)),
) -> Option(#(String, Option(String))) {
  case items {
    [TokenValue(name_tok)] -> {
      Some(#(name_tok.value, None))
    }
    [TokenValue(name_tok), TokenValue(_colon), TokenValue(type_tok)] -> {
      Some(#(name_tok.value, Some(type_tok.value)))
    }
    [TokenValue(name_tok), _] -> {
      Some(#(name_tok.value, None))
    }
    [TokenValue(name_tok), _, _] -> {
      Some(#(name_tok.value, None))
    }
    _ -> None
  }
}

/// Helper to create if expression AST.
fn make_if(values) -> Expr {
  // The structure is: [if_kw, cond, then_block, else_kw, else_block]
  let cond = case values {
    [_, AstValue(c), ..] -> c
    _ -> panic as "If: expected condition"
  }

  let then_block = case values {
    [_, _, AstValue(b), ..] -> b
    _ -> panic as "If: expected then block"
  }

  let else_block = case values {
    [_, _, _, _, AstValue(b)] -> b
    _ -> panic as "If: expected else block"
  }

  // Get span from if keyword
  let if_kw = case values {
    [KeywordValue(kw), ..] -> kw
    _ -> panic as "If: expected keyword"
  }

  let start_span = Span("tao", if_kw.line, if_kw.column, if_kw.line, if_kw.column + 2)
  let end_span = get_expr_span(else_block)
  let full_span = Span(start_span.file, start_span.start_line, start_span.start_col, end_span.end_line, end_span.end_col)

  // Convert blocks to expressions
  let then_expr = block_to_expr(then_block)
  let else_expr = block_to_expr(else_block)

  If(cond, then_expr, Some(else_expr), full_span)
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

  // Extract clauses: the structure is [match, scrut, LBrace, ListValue(clauses), RBrace]
  // or [match, scrut, Arrow, Type, LBrace, ListValue(clauses), RBrace] with type annotation
  // Note: many(seq(...)) creates ListValue([ListValue(clause1), ListValue(clause2), ...])
  let clauses = case values {
    [_, _, TokenValue(lbrace), ListValue(nested), _] if lbrace.value == "{" -> {
      // No type annotation: [match, scrut, LBrace, ListValue, RBrace]
      extract_clauses_from_nested(nested, [])
    }
    [_, _, _, _, TokenValue(lbrace), ListValue(nested), _] if lbrace.value == "{" -> {
      // With type annotation: [match, scrut, Arrow, Type, LBrace, ListValue, RBrace]
      extract_clauses_from_nested(nested, [])
    }
    _ -> {
      // Fallback: try to extract clauses directly from values
      extract_match_clauses(values, [])
    }
  }

  let start_span = Span("tao", match_kw.line, match_kw.column, match_kw.line, match_kw.column + 5)
  let end_span = get_expr_span(scrut)
  let full_span = Span(start_span.file, start_span.start_line, start_span.start_col, end_span.end_line, end_span.end_col)
  Match(scrut, clauses, full_span)
}

fn extract_clauses_from_nested(nested_values: List(Value(Expr)), acc: List(MatchClause)) -> List(MatchClause) {
  // nested_values could be:
  // 1. ListValue([ListValue(clause1), ListValue(clause2), ...]) - nested
  // 2. ListValue([Pipe, pattern, opt_if, Arrow, body, Pipe, pattern, ...]) - flat
  // Try to detect which case and handle accordingly
  case nested_values {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // Check if items looks like a clause (starts with Pipe)
      case items {
        [TokenValue(pipe), ..] if pipe.value == "|" -> {
          // Nested case: each item is a clause
          let clause_clauses = extract_clauses(items, [])
          extract_clauses_from_nested(rest, list.append(clause_clauses, acc))
        }
        _ -> {
          // Not a clause, try flat case
          extract_clauses(nested_values, acc)
        }
      }
    }
    [TokenValue(pipe), ..] if pipe.value == "|" -> {
      // Flat case: all clauses are in the same list
      extract_clauses(nested_values, acc)
    }
    [_v, ..rest] -> {
      // Skip non-clause items
      extract_clauses_from_nested(rest, acc)
    }
  }
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
    // Guard wrapped in ListValue (from seq([keyword_pattern("if"), ref("Expr")]))
    [ListValue([KeywordValue(_if), AstValue(guard_expr)]), TokenValue(_arrow), AstValue(body), ..rest] -> {
      Some(#(pattern, Some(guard_expr), body, rest))
    }
    // Guard as flat list
    [KeywordValue(_if), AstValue(guard_expr), TokenValue(_arrow), AstValue(body), ..rest] -> {
      Some(#(pattern, Some(guard_expr), body, rest))
    }
    // No guard
    [TokenValue(_arrow), AstValue(body), ..rest] -> {
      Some(#(pattern, None, body, rest))
    }
    _ -> None
  }
}

pub fn pattern_ast_to_pattern(expr: Expr) -> Pattern {
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
    [ListValue(items), ..rest] -> {
      // Each param is wrapped in a ListValue
      // Extract the param name from items
      let param = extract_single_param(items)
      case param {
        Some(name) -> extract_params_from_many(rest, [#(name, None), ..acc])
        None -> extract_params_from_many(rest, acc)
      }
    }
    [_, ..rest] -> extract_params_from_many(rest, acc)
  }
}

fn extract_single_param(items: List(Value(Expr))) -> Option(String) {
  case items {
    [TokenValue(name_tok)] -> Some(name_tok.value)
    [TokenValue(name_tok), _] -> Some(name_tok.value)
    [TokenValue(name_tok), _, _] -> Some(name_tok.value)
    _ -> None
  }
}

/// Extract params with type annotations from many result.
/// Each param is: ListValue([TokenValue(name), opt([":", TypeRuleResult])])
/// TypeRuleResult contains nested structure with full type info
fn extract_params_from_many_with_types(params_many: List(Value(Expr)), acc: List(#(String, Option(String)))) -> List(#(String, Option(String))) {
  case params_many {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // Each param is [TokenValue(name), opt([":", TypeResult])]
      case items {
        [TokenValue(name_tok), TokenValue(_colon), ..type_values] -> {
          // Reconstruct type string from type_values
          let type_str = reconstruct_type_string(type_values)
          extract_params_from_many_with_types(rest, [#(name_tok.value, Some(type_str)), ..acc])
        }
        [TokenValue(name_tok), ..] ->
          extract_params_from_many_with_types(rest, [#(name_tok.value, None), ..acc])
        _ -> extract_params_from_many_with_types(rest, acc)
      }
    }
    [_, ..rest] -> extract_params_from_many_with_types(rest, acc)
  }
}

/// Reconstruct type string from Type rule values.
fn reconstruct_type_string(type_values: List(Value(Expr))) -> String {
  reconstruct_type_loop(type_values, "")
}

fn reconstruct_type_loop(type_values: List(Value(Expr)), acc: String) -> String {
  case type_values {
    [] -> acc
    [TokenValue(t), ..rest] -> {
      case t.kind {
        "fn" -> reconstruct_type_loop(rest, acc <> "fn(")
        "LParen" -> reconstruct_type_loop(rest, acc <> "(")
        "RParen" -> reconstruct_type_loop(rest, acc <> ")")
        "Arrow" -> reconstruct_type_loop(rest, acc <> " -> ")
        "Comma" -> reconstruct_type_loop(rest, acc <> ", ")
        "Ident" -> reconstruct_type_loop(rest, acc <> t.value)
        _ -> reconstruct_type_loop(rest, acc)
      }
    }
    [KeywordValue(t), ..rest] -> {
      // Handle keywords like "fn"
      case t.kind {
        "fn" -> reconstruct_type_loop(rest, acc <> "fn(")
        _ -> reconstruct_type_loop(rest, acc)
      }
    }
    [ListValue(nested), ..rest] -> {
      // Handle nested type (e.g., function type params)
      let nested_str = reconstruct_type_loop(nested, "")
      reconstruct_type_loop(rest, acc <> nested_str)
    }
    [ParensValue(nested), ..rest] -> {
      // Handle parenthesized types
      let nested_str = reconstruct_type_loop(nested, "")
      reconstruct_type_loop(rest, acc <> nested_str)
    }
    [_, ..rest] -> reconstruct_type_loop(rest, acc)
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
    [AstValue(func), ListValue(call_items)] -> {
      // call_items is flattened: [LParen, ListValue(arg1_items), ListValue(arg2_items), RParen]
      // Extract the args (everything between LParen and RParen)
      let args = extract_args_from_flattened_call(call_items, [])
      let span = get_expr_span(func)
      App(func, args, span)
    }
    [AstValue(func)] -> func
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }
}

fn extract_args_from_flattened_call(
  call_items: List(Value(Expr)),
  acc: List(Expr),
) -> List(Expr) {
  case call_items {
    [] -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.value == "(" -> {
      // Skip LParen, start collecting args
      extract_args_from_flattened_call(rest, acc)
    }
    [TokenValue(t), ..rest] if t.value == ")" -> {
      // End of args
      list.reverse(acc)
    }
    [TokenValue(t), ..rest] if t.value == "," -> {
      // Skip comma
      extract_args_from_flattened_call(rest, acc)
    }
    [AstValue(e), ..rest] -> {
      // Direct expression
      extract_args_from_flattened_call(rest, [e, ..acc])
    }
    [ListValue(arg_items), ..rest] -> {
      // arg_items is [Expr, opt_comma] or nested structures
      // Extract all AstValue from arg_items
      let extracted = extract_all_exprs(arg_items, [])
      extract_args_from_flattened_call(rest, list.append(list.reverse(extracted), acc))
    }
    [_, ..rest] -> {
      // Skip other items
      extract_args_from_flattened_call(rest, acc)
    }
  }
}

fn extract_all_exprs(items: List(Value(Expr)), acc: List(Expr)) -> List(Expr) {
  case items {
    [] -> acc
    [AstValue(e), ..rest] -> extract_all_exprs(rest, [e, ..acc])
    [ListValue(nested), ..rest] -> extract_all_exprs(rest, list.append(extract_all_exprs(nested, []), acc))
    [_, ..rest] -> extract_all_exprs(rest, acc)
  }
}

fn extract_args_from_flattened(
  calls: List(Value(Expr)),
  in_parens: Bool,
  acc: List(Expr),
) -> List(Expr) {
  case calls {
    [] -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.value == "(" -> {
      // Start of args
      extract_args_from_flattened(rest, True, acc)
    }
    [TokenValue(t), ..rest] if t.value == ")" -> {
      // End of args - return what we have
      list.reverse(acc)
    }
    [ListValue([AstValue(e)]), ..rest] if in_parens -> {
      // Wrapped arg
      extract_args_from_flattened(rest, in_parens, [e, ..acc])
    }
    [ListValue(items), ..rest] if in_parens -> {
      // Try to extract from multi-item ListValue
      case items {
        [AstValue(e)] -> extract_args_from_flattened(rest, in_parens, [e, ..acc])
        [AstValue(e), ..] -> extract_args_from_flattened(rest, in_parens, [e, ..acc])
        _ -> extract_args_from_flattened(rest, in_parens, acc)
      }
    }
    [AstValue(e), ..rest] if in_parens -> {
      // Unwrapped arg
      extract_args_from_flattened(rest, in_parens, [e, ..acc])
    }
    [_, ..rest] -> {
      // Skip other items
      extract_args_from_flattened(rest, in_parens, acc)
    }
  }
}

fn extract_wrapped_args(args_wrapped: List(Value(Expr)), acc: List(Expr)) -> List(Expr) {
  case args_wrapped {
    [] -> list.reverse(acc)
    [ListValue(items), ..rest] -> {
      // items is [AstValue(arg), opt_comma]
      case list.first(items) {
        Ok(AstValue(e)) -> extract_wrapped_args(rest, [e, ..acc])
        _ -> extract_wrapped_args(rest, acc)
      }
    }
    [AstValue(e), ..rest] -> extract_wrapped_args(rest, [e, ..acc])
    [_, ..rest] -> extract_wrapped_args(rest, acc)
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
      AstValue(param_type_expr),  // param type (parsed as Expr)
      _,  // ")"
      _,  // "->"
      AstValue(return_type_expr),  // return type (parsed as Expr)
      AstValue(body),  // body
    ] -> {
      // Extract type names from expressions
      let param_type_str = expr_to_type_string(param_type_expr)
      let return_type_str = expr_to_type_string(return_type_expr)
      OverloadedFn(
        name_token.value,
        "T",  // type param (simplified for now)
        param_name_token.value,
        param_type_str,
        return_type_str,
        body,
        span_from_token(name_token, "tao"),
      )
    }
    _ -> panic as "Expected overloaded function definition"
  }
}

/// Extract type name from a type expression.
fn expr_to_type_string(expr: Expr) -> String {
  case expr {
    Var(name, _) -> name
    Int(n, _) -> int.to_string(n)
    _ -> "Unknown"
  }
}

/// Helper to create import AST.
fn make_import(values) -> Expr {
  // Check if the values contain LBrace (selective import)
  let has_selective = has_lbrace(values)

  case has_selective {
    True -> {
      // Parse selective import
      let path = extract_module_path(values)
      let names = extract_selective_names_from_values(values)
      let import_item = ImportSelective(path, names, Span("import", 0, 0, 0, 0))
      Import(import_item, get_import_span(values))
    }
    False -> {
      // Simple module import
      let path = extract_module_path(values)
      let import_item = ImportModule(path, Span("import", 0, 0, 0, 0))
      Import(import_item, get_import_span(values))
    }
  }
}

fn has_lbrace(values: List(Value(a))) -> Bool {
  list.any(values, fn(v) {
    case v {
      TokenValue(t) if t.kind == "LBrace" -> True
      ListValue(inner) -> has_lbrace(inner)
      _ -> False
    }
  })
}

fn extract_module_path(values: List(Value(a))) -> String {
  // Extract Ident tokens until we hit LBrace or end
  extract_path_until_brace(values, [])
  |> string.join("/")
}

fn extract_path_until_brace(values: List(Value(a)), acc: List(String)) -> List(String) {
  case values {
    [] -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.kind == "LBrace" -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.kind == "Ident" -> {
      extract_path_until_brace(rest, [t.value, ..acc])
    }
    [ListValue(inner), ..rest] -> {
      // Check if inner contains LBrace
      case has_lbrace(inner) {
        True -> list.reverse(acc)
        False -> {
          let inner_parts = extract_path_until_brace(inner, [])
          extract_path_until_brace(rest, list.append(inner_parts, acc))
        }
      }
    }
    [_v, ..rest] -> {
      extract_path_until_brace(rest, acc)
    }
  }
}

fn extract_selective_names_from_values(values: List(Value(a))) -> List(ImportItem) {
  // Find LBrace and extract Ident tokens until RBrace
  extract_names_after_lbrace(values, False, [])
}

fn extract_names_after_lbrace(
  values: List(Value(a)),
  in_braces: Bool,
  acc: List(ImportItem),
) -> List(ImportItem) {
  case values {
    [] -> list.reverse(acc)
    [TokenValue(t), ..rest] if t.kind == "LBrace" -> {
      extract_names_after_lbrace(rest, True, acc)
    }
    [TokenValue(t), ..rest] if t.kind == "RBrace" -> {
      list.reverse(acc)
    }
    [TokenValue(t), ..rest] if in_braces && t.kind == "Ident" -> {
      extract_names_after_lbrace(rest, in_braces, [ImportName(t.value, None), ..acc])
    }
    [ListValue(inner), ..rest] -> {
      let inner_names = extract_names_after_lbrace(inner, in_braces, [])
      extract_names_after_lbrace(rest, in_braces, list.append(inner_names, acc))
    }
    [_v, ..rest] -> {
      extract_names_after_lbrace(rest, in_braces, acc)
    }
  }
}

fn get_import_span(values: List(Value(a))) -> Span {
  case values {
    [TokenValue(t), ..] -> Span("import", t.line, t.column, t.line, t.column + string.length(t.value))
    [KeywordValue(t), ..] -> Span("import", t.line, t.column, t.line, t.column + string.length(t.value))
    [ListValue(inner), ..] -> get_import_span(inner)
    _ -> Span("import", 0, 0, 0, 0)
  }
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
      // Has type: skip ":" and extract type from Type rule result
      let without_colon = list.drop(rest_after_name, 1)
      let type_annotation = case list.first(without_colon) {
        Ok(AstValue(Var(type_name, _))) -> Some(type_name)  // Simple type from Var
        Ok(TokenValue(t)) -> Some(t.value)  // Fallback for simple token
        _ -> None
      }
      let without_type = list.drop(without_colon, 1)
      let without_eq = list.drop(without_type, 1)
      #(type_annotation, without_eq)
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

/// Helper to create for loop AST.
fn make_for(values) -> Expr {
  // values = [for_kw, pattern_expr, in_kw, collection_expr, block]
  case values {
    [_, AstValue(pattern_expr), _, AstValue(collection), AstValue(block_expr)] -> {
      let pattern = pattern_ast_to_pattern(pattern_expr)
      let body = case block_expr {
        Block(stmts, _) -> stmts
        _ -> [block_expr]
      }
      let span = Span("tao", 0, 0, 0, 0)  // TODO: get proper span
      For(pattern, collection, body, span)
    }
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }
}

/// Helper to create while loop AST.
fn make_while(values) -> Expr {
  // values = [while_kw, condition_expr, block]
  case values {
    [_, AstValue(condition), AstValue(block_expr)] -> {
      let body = case block_expr {
        Block(stmts, _) -> stmts
        _ -> [block_expr]
      }
      let span = Span("tao", 0, 0, 0, 0)  // TODO: get proper span
      While(condition, body, span)
    }
    _ -> Int(0, Span("error", 0, 0, 0, 0))
  }
}

/// Helper to create loop AST.
fn make_loop(values) -> Expr {
  // values = [loop_kw, block]
  case values {
    [_, AstValue(block_expr)] -> {
      let body = case block_expr {
        Block(stmts, _) -> stmts
        _ -> [block_expr]
      }
      let span = Span("tao", 0, 0, 0, 0)  // TODO: get proper span
      Loop(body, span)
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
    Float(f, _) -> float.to_string(f)
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
    If(cond, then_expr, else_expr, _) -> {
      let else_str = case else_expr {
        Some(e) -> " else { " <> format_expr(e) <> " }"
        None -> ""
      }
      "if " <> format_expr(cond) <> " { " <> format_expr(then_expr) <> " }" <> else_str
    }
    For(pattern, collection, body, _) -> {
      let pattern_str = format_pattern(pattern)
      let body_str = string_join(list.map(body, format_expr), "; ")
      "for " <> pattern_str <> " in " <> format_expr(collection) <> " { " <> body_str <> " }"
    }
    While(condition, body, _) -> {
      let body_str = string_join(list.map(body, format_expr), "; ")
      "while " <> format_expr(condition) <> " { " <> body_str <> " }"
    }
    Loop(body, _) -> {
      let body_str = string_join(list.map(body, format_expr), "; ")
      "loop { " <> body_str <> " }"
    }
    Break(_) -> "break"
    Continue(_) -> "continue"
    Test(name, body, _) -> {
      "test \"" <> name <> "\" " <> format_expr(body)
    }
    Run(value, _) -> {
      "run " <> format_expr(value)
    }
    Import(import_item, _) -> {
      "import " <> format_import_item(import_item)
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

fn format_import_item(item: Import) -> String {
  case item {
    ImportModule(path, _) -> path
    ImportAlias(path, alias, _) -> path <> " as " <> alias
    ImportSelective(path, names, _) -> {
      path <> ".{ " <> string_join(list.map(names, format_import_name), ", ") <> " }"
    }
    ImportSelectiveAlias(path, alias, names, _) -> {
      path <> " as " <> alias <> ".{ " <> string_join(list.map(names, format_import_name), ", ") <> " }"
    }
    ImportWildcard(path, _) -> path <> " as *"
  }
}

fn format_import_name(item: ImportItem) -> String {
  case item {
    ImportName(name, None) -> name
    ImportName(name, Some(alias)) -> name <> " as " <> alias
    ImportType(name, None) -> name
    ImportType(name, Some(alias)) -> name <> " as " <> alias
    ImportOperator(name, None) -> name
    ImportOperator(name, Some(alias)) -> name <> " as " <> alias
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

// ============================================================================
// TYPE HELPERS
// ============================================================================

/// Convert AstType to string representation.
fn type_to_string(t: AstType) -> String {
  case t {
    TVar(name) -> name
    TApp(name, args) -> {
      case args {
        [] -> name
        _ -> name <> "(" <> string_join(list.map(args, type_to_string), ", ") <> ")"
      }
    }
    TFn(params, ret) -> {
      "fn(" <> string_join(list.map(params, type_to_string), ", ") <> ") -> " <> type_to_string(ret)
    }
    TRecord(_) -> "{...}"
    TTuple(_) -> "(...)"
    THole -> "_"
  }
}
