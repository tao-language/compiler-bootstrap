/// Tao High-Level Language Abstract Syntax Tree
///
/// The Tao language is a high-level language that desugars to Core.
/// This module defines the AST types for Tao source code before desugaring.
///
/// All terms use string-based variable names (before De Bruijn conversion
/// by the desugarer).

import gleam/option.{type Option}
import syntax/span.{type Span}

// ============================================================================
// LITERALS
// ============================================================================

/// Literal values in the Tao language.
pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

// ============================================================================
// EXPRESSIONS
// ============================================================================

/// High-level expressions (string-based variable names, before desugaring).
///
/// These are the syntactic constructs that the parser produces.
/// The desugarer converts these to Core terms (De Bruijn indices).
pub type Expr {
  /// Variable: x
  Var(name: String, span: Span)

  /// Literal: 42, 3.14
  Lit(value: Literal, span: Span)

  /// Lambda: fn(x: a) -> a
  Lambda(params: List(Param), body: Expr, span: Span)

  /// Application: f(x)
  Call(fun: Expr, args: List(Expr), span: Span)

  /// Binary operator: a + b
  BinOp(left: Expr, op: BinOp, right: Expr, span: Span)

  /// Unary operator: -x, !x
  UnaryOp(op: UnaryOp, operand: Expr, span: Span)

  /// Record construction: { x: 1, y: 2 }
  Record(fields: List(#(String, Expr)), span: Span)

  /// Field access: record.field
  FieldAccess(record: Expr, field: String, span: Span)

  /// Constructor: Some(x), None, True, False
  Ctr(name: String, args: List(Expr), span: Span)

  /// Pattern match: match x { | Some(y) -> y | None -> 0 }
  Match(arg: Expr, clauses: List(MatchClause), span: Span)

  /// If expression: if cond { a } else { b }
  If(cond: Expr, then: Expr, else_: Option(Expr), span: Span)

  /// Type annotation: (e : T)
  Ann(term: Expr, type_: TypeAst, span: Span)

  /// Hole: _
  Hole(span: Span)

  /// Record spread: ..record (used in record updates)
  Spread(record: Expr, span: Span)

  /// Record field query: point.{x, sum: x + y}
  FieldQuery(record: Expr, fields: List(#(String, Expr)), span: Span)
}

/// Binary operators.
///
/// These desugar to Core variable references:
/// - OpAdd → Var("+")
/// - OpSub → Var("-")
/// - etc.
pub type BinOp {
  OpAdd
  OpSub
  OpMul
  OpDiv
  OpEq
  OpNeq
  OpLt
  OpGt
  OpLte
  OpGte
  OpAnd
  OpOr
  OpPipe
}

/// Unary operators.
///
/// These desugar to Core variable references:
/// - OpNegate → Var("-") (unary negation)
/// - OpNot → Var("not")
pub type UnaryOp {
  OpNegate
  OpNot
}

// ============================================================================
// STATEMENTS
// ============================================================================

/// Module-level statements.
///
/// A Tao module is a list of statements. The desugarer converts
/// these into a chain of $let bindings plus a final record return.
pub type Stmt {
  /// let x [: Type] = expr
  Let(name: String, type_: Option(TypeAst), value: Expr, span: Span)

  /// fn name(params) [: Type] { body }
  Fn(name: String, params: List(Param), type_: Option(TypeAst), body: Expr, span: Span)

  /// import path [as alias] { names }
  Import(path: String, alias: Option(String), names: List(#(String, Option(String))), span: Span)

  /// type Name = Ctor | Ctor(args) | ...
  TypeDef(name: String, params: List(#(String, TypeAst)), constructors: List(Constructor), span: Span)

  /// Test expression (REPL-style): > expr [~> expected]
  /// Or multiline: > expr \n expected
  Test(name: String, expr: Expr, expected: Option(Pattern), span: Span)

  /// Expression statement: expr (discarded result)
  Expr(expr: Expr, span: Span)
}

// ============================================================================
// PATTERNS
// ============================================================================

/// Patterns used in match expressions and let bindings.
pub type Pattern {
  /// Wildcard: _
  PAny(span: Span)

  /// Variable: x (binds to anything)
  PVar(name: String, span: Span)

  /// Literal: 42, 3.14
  PLit(value: Literal, span: Span)

  /// Constructor: Some(x), None, True, False
  PCtr(name: String, arg: Pattern, span: Span)

  /// Record pattern: { x, y }
  PRecord(fields: List(#(String, Pattern)), span: Span)
}

// ============================================================================
// MATCH CLAUSES
// ============================================================================

/// A single match clause: pattern -> body [if guard]
pub type MatchClause {
  MatchClause(
    pattern: Pattern,
    guard: Option(Expr),
    body: Expr,
    span: Span,
  )
}

// ============================================================================
// FUNCTION PARAMETERS
// ============================================================================

/// A function parameter with optional type annotation.
///
/// fn add(x: Int, y: Int) -> Int
///         ^^^^^^
pub type Param {
  Param(name: String, type_: Option(TypeAst), span: Span)
}

// ============================================================================
// TYPE AST
// ============================================================================

/// Type annotations in Tao source (before desugaring).
pub type TypeAst {
  /// Type variable: a, b, T
  TVar(name: String, span: Span)

  /// Type application: Maybe(a), List(Int)
  TApp(name: String, args: List(TypeAst), span: Span)

  /// Function type: (Int, Int) -> Int
  TFn(args: List(TypeAst), ret: TypeAst, span: Span)

  /// Record type: { x: Int, y: Int = 0 }
  TRecord(fields: List(#(String, TypeAst, Option(Expr))), span: Span)

  /// Tuple type: (Int, String)
  TTuple(fields: List(TypeAst), span: Span)

  /// Hole: _ (wildcard type)
  THole(span: Span)
}

// ============================================================================
// TYPE CONSTRUCTORS
// ============================================================================

/// A type constructor definition.
///
/// type Style {
///   | Default
///   | Padded(Int)
///   | Button(text: String, style: Style = Default)
/// }
pub type Constructor {
  Constructor(
    name: String,
    fields: List(#(String, TypeAst, Option(Expr))),
    span: Span,
  )
}
