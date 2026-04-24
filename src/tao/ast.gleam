// Tao AST - High-level expressions and statements
// Tao is the user-facing language that desugars to Core.

import syntax/span.{type Span}
import gleam/option.{type Option}

// ============================================================================
// TAo EXPRESSIONS
// ============================================================================

/// High-level expressions (string-based variable names)
pub type Expr {
  Var(name: String, span: Span)
  Lit(value: Literal, span: Span)
  Lambda(params: List(Param), body: Expr, span: Span)
  Call(fun: Expr, args: List(Expr), span: Span)
  BinOp(left: Expr, op: BinOp, right: Expr, span: Span)
  Ctr(name: String, args: List(Expr), span: Span)
  Match(arg: Expr, cases: List(MatchClause), span: Span)
  If(cond: Expr, then: Expr, else_: Expr, span: Span)
  Ann(term: Expr, typ: TypeAst, span: Span)
  Hole(span: Span)
  Record(fields: List(#(String, Expr)), span: Span)
  Dot(record: Expr, field: String, span: Span)
}

/// BinOp operators
pub type BinOp {
  Add
  Sub
  Mul
  Div
  Eq
  Neq
  Lt
  Gt
  Le
  Ge
  And
  Or
}

/// Literals
pub type Literal {
  IntLit(value: Int)
  FloatLit(value: Float)
  StringLit(value: String)
}

// ============================================================================
// TAo PATTERNs
// ============================================================================

/// Patterns for match expressions
pub type Pattern {
  PatVar(name: String, span: Span)
  PatLit(literal: Literal, span: Span)
  PatConstr(name: String, patterns: List(Pattern), span: Span)
  PatDot(record: Pattern, field: String, span: Span)
}

// ============================================================================
// TAo MATCH CLAUSES
// ============================================================================

/// A single match clause
pub type MatchClause {
  MatchClause(pattern: Pattern, body: Expr, guard: Option(Expr), span: Span)
}

// ============================================================================
// TAo PARAMETERS
// ============================================================================

/// Function parameters
pub type Param {
  Param(name: String, type_: Option(TypeAst), span: Span)
}

// ============================================================================
// TAo TYPE AST
// ============================================================================

/// Type annotations in Tao source
pub type TypeAst {
  TVar(name: String, span: Span)
  TApp(name: String, args: List(TypeAst), span: Span)
  TFn(args: List(TypeAst), ret: TypeAst, span: Span)
  THole(span: Span)
}

// ============================================================================
// TAo STATEMENTS
// ============================================================================

/// Top-level statements
pub type Stmt {
  Let(name: String, value: Expr, span: Span)
  Fn(name: String, params: List(Param), body: Expr, span: Span)
  Import(path: String, span: Span)
  TypeDef(name: String, constructors: List(#(String, List(#(String, TypeAst)))), span: Span)
  For(name: String, collection: Expr, body: Expr, span: Span)
  While(cond: Expr, body: Expr, span: Span)
  Expr(expr: Expr, span: Span)  // expression statement
}

// ============================================================================
// TAo MODULE
// ============================================================================

/// A Tao module
pub type Module {
  Module(name: String, statements: List(Stmt), span: Span)
}
