import syntax/grammar.{Span, type Span}
import gleam/option.{type Option}

// ============================================================================
// TAO ABSTRACT SYNTAX TREE
// ============================================================================
// High-level syntax tree for Tao language following the updated syntax design:
// - Untyped literals (Int, Float, String only)
// - Bool is a sum type (True | False), not a literal
// - Explicit type parameters: fn<a>(x: a) -> a
// - Sum types: type Maybe(a) = Some(a) | None
// - Pattern matching: match x { | Some(y) -> y | None -> 0 }
// - Modules: _prefix = private, everything else public
// - do { ... } for imperative blocks
// - comptime expr (use comptime do { } for blocks)

pub type Program {
  Program(
    module: Option(String),
    imports: List(Import),
    declarations: List(Declaration),
  )
}

pub type Import {
  /// import math
  /// import math as m
  /// import math { min, max }
  /// import math as m { min, max }
  /// import math *
  Import(module: String, alias: Option(String), names: Option(ImportNames))
}

pub type ImportNames {
  /// import math *
  ImportAll
  /// import math { min, max, abs }
  /// import math { min as mn, max }
  ImportSome(List(ImportName))
}

pub type ImportName {
  ImportName(name: String, alias: Option(String))
}

pub type Declaration {
  /// let x = 5
  /// let mut counter = 0
  Let(LetDecl)
  /// fn add<a>(a: Int, b: Int) -> Int { a + b }
  Fn(FnDecl)
  /// type Point = { x: Int, y: Int }
  /// type String = List(Char)
  TypeAlias(TypeAliasDecl)
  /// type Maybe(a) = Some(a) | None
  /// type Bool = True | False
  TypeDef(TypeDefDecl)
}

// ============================================================================
// LET DECLARATIONS
// ============================================================================

pub type LetDecl {
  LetDecl(
    name: String,
    mutability: Mutability,
    type_annotation: Option(Type),
    value: Expr,
    span: Span,
  )
}

pub type Mutability {
  Immutable
  Mutable
}

// ============================================================================
// FUNCTION DECLARATIONS
// ============================================================================

pub type FnDecl {
  FnDecl(
    name: String,
    /// Explicit type parameters: <a, b>
    type_params: List(String),
    params: List(Param),
    return_type: Option(Type),
    body: Expr,
    attributes: List(Attribute),
    span: Span,
  )
}

pub type Param {
  Param(name: String, type_annotation: Option(Type), span: Span)
}

// ============================================================================
// TYPE DECLARATIONS
// ============================================================================

pub type TypeAliasDecl {
  TypeAliasDecl(
    name: String,
    type_params: List(String),
    type_: Type,
    span: Span,
  )
}

pub type TypeDefDecl {
  TypeDefDecl(
    name: String,
    type_params: List(String),
    /// Sum type constructors: [Some(a), None]
    constructors: List(Constructor),
    span: Span,
  )
}

pub type Constructor {
  Constructor(
    name: String,
    fields: List(ConstructorField),
    span: Span,
  )
}

pub type ConstructorField {
  /// Named field: Some(value: a)
  NamedField(name: String, type_: Type)
  /// Unnamed field: Some(a)
  UnnamedField(type_: Type)
}

// ============================================================================
// EXPRESSIONS
// ============================================================================

pub type Expr {
  /// Variable reference: x
  Var(name: String, span: Span)

  /// Literal: 42, 3.14, "hello"
  /// Note: true/false are constructors, not literals
  Lit(Literal, span: Span)

  /// Lambda: fn(x) { x + 1 }
  /// Lambda with type params: fn<a>(x: a) -> a
  Lambda(List(String), List(Param), Expr, Span)

  /// Function call: f(x, y)
  Call(Expr, List(Expr), Span)

  /// Binary operator: a + b
  BinOp(Expr, BinOperator, Expr, Span)

  /// Unary operator: -x, !x
  UnaryOp(UnaryOperator, Expr, Span)

  /// Field access: record.field
  FieldAccess(Expr, String, Span)

  /// Optional chaining: user?.address
  OptionalChain(Expr, String, Span)

  /// Record construction: { x: 1, y: 2 }
  Record(List(RecordField), Span)

  /// Record update: { ..old, x: 1 }
  RecordUpdate(Expr, List(RecordField), Span)

  /// List: [1, 2, 3]
  List(List(Expr), Span)

  /// Tuple: (a, b, c)
  /// Unit: ()
  Tuple(List(Expr), Span)

  /// Constructor: Some(x), None, True, False
  Ctr(String, List(Expr), Span)

  /// Match expression: match x { | Some(y) -> y | None -> 0 }
  Match(Expr, List(MatchClause), Span)

  /// Let binding in expression position: let x = e1 in e2
  LetExpr(LetDecl, Expr, Span)

  /// Imperative block: do { mut x = 0; x = x + 1; x }
  Block(List(BlockStatement), Span)

  /// If expression: if cond { a } else { b }
  If(Expr, Expr, Option(Expr), Span)

  /// Result bind: let x <- e1 in e2
  Bind(String, Expr, Expr, Span)

  /// Result unwrap: e?
  ResultUnwrap(Expr, Span)

  /// Type annotation: (e: T)
  Annotated(Expr, Type, Span)

  /// Comptime expression: comptime factorial(5)
  /// Comptime block: comptime do { ... }
  Comptime(Expr, Span)

  /// Hole: _
  Hole(Span)
}

pub type RecordField {
  RecordField(name: String, value: Expr)
}

pub type BlockStatement {
  /// Mutable let: mut x = 0
  StmtLet(LetDecl)
  /// Assignment: x = value
  StmtAssign(String, Expr)
  /// Expression statement: print(x)
  StmtExpr(Expr)
}

pub type MatchClause {
  /// Pattern with optional guard: x if x > 0 -> ...
  MatchClause(
    pattern: Pattern,
    guard: Option(Expr),
    body: Expr,
    span: Span,
  )
}

// ============================================================================
// PATTERNS
// ============================================================================

pub type Pattern {
  /// Wildcard: _
  PAny(Span)

  /// Variable: x
  PVar(String, Span)

  /// Literal: 42
  PLit(Literal, Span)

  /// Constructor: Some(x), Cons(h, t), True, False
  PCtr(String, List(Pattern), Span)

  /// Record: { x, y }
  PRecord(List(String), Span)

  /// Tuple: (a, b)
  PTuple(List(Pattern), Span)

  /// List: [h, ..t]
  PList(List(Pattern), Option(String), Span)

  /// Or pattern: Some(0) | None
  POr(List(Pattern), Span)

  /// As pattern: x @ Some(_)
  PAs(Pattern, String, Span)
}

// ============================================================================
// TYPES
// ============================================================================

pub type Type {
  /// Type variable: a, b, t
  TVar(String)

  /// Type application: Maybe(a), List(Int)
  TApp(String, List(Type))

  /// Function type: (Int, Int) -> Int
  TFn(List(Type), Type)

  /// Record type: { x: Int, y: Int }
  TRecord(List(#(String, Type)))

  /// Tuple type: (Int, String)
  /// Unit type: ()
  TTuple(List(Type))

  /// Hole: _
  THole
}

// Note: No primitive types! Bool, String, Unit are all defined in stdlib:
// type Bool = True | False
// type String = List(Char)
// type Unit = ()

// ============================================================================
// LITERALS
// ============================================================================
// Literals are UNTYPED. They're just values. Type inference determines
// the actual type (Int defaults to I32, Float defaults to F64).
// Type checking validates that values fit in the constrained type.

pub type Literal {
  /// Integer literal (e.g., 42, -1, 0)
  /// Type inference determines: I32, I64, U32, U64, F32, F64
  Int(Int)
  /// Float literal (e.g., 3.14, -0.5, 1.0)
  /// Type inference determines: F32, F64
  Float(Float)
  /// String literal (e.g., "hello", "world\n")
  String(String)
}

// Note: true/false are NOT literals. They're constructors:
// type Bool = True | False

// ============================================================================
// OPERATORS
// ============================================================================

pub type BinOperator {
  /// Arithmetic: +, -, *, /, %
  OpAdd
  OpSub
  OpMul
  OpDiv
  OpMod

  /// Comparison: ==, !=, <, >, <=, >=
  OpEq
  OpNeq
  OpLt
  OpGt
  OpLte
  OpGte

  /// Logical: &&, ||
  OpAnd
  OpOr

  /// Pipe: |>
  OpPipe

  /// String concat: <>
  OpConcat
}

pub type UnaryOperator {
  /// Negation: -
  OpNegate

  /// Logical not: !
  OpNot
}

// ============================================================================
// ATTRIBUTES
// ============================================================================

pub type Attribute {
  /// @permission(Read("/tmp"))
  AttrPermission(Permission)

  /// @effect(IO)
  AttrEffect(String)

  /// @inline
  AttrInline

  /// @comptime
  AttrComptime
}

pub type Permission {
  PermRead(String)
  PermWrite(String)
  PermAll
}

// ============================================================================
// SPAN HELPERS
// ============================================================================

pub fn span_from_expr(expr: Expr) -> Span {
  case expr {
    Var(_, span) -> span
    Lit(_, span) -> span
    Lambda(_, _, _, span) -> span
    Call(_, _, span) -> span
    BinOp(_, _, _, span) -> span
    UnaryOp(_, _, span) -> span
    FieldAccess(_, _, span) -> span
    OptionalChain(_, _, span) -> span
    Record(_, span) -> span
    RecordUpdate(_, _, span) -> span
    List(_, span) -> span
    Tuple(_, span) -> span
    Ctr(_, _, span) -> span
    Match(_, _, span) -> span
    LetExpr(_, _, span) -> span
    Block(_, span) -> span
    If(_, _, _, span) -> span
    Bind(_, _, _, span) -> span
    ResultUnwrap(_, span) -> span
    Annotated(_, _, span) -> span
    Comptime(_, span) -> span
    Hole(span) -> span
  }
}

pub fn span_from_pattern(pattern: Pattern) -> Span {
  case pattern {
    PAny(span) -> span
    PVar(_, span) -> span
    PLit(_, span) -> span
    PCtr(_, _, span) -> span
    PRecord(_, span) -> span
    PTuple(_, span) -> span
    PList(_, _, span) -> span
    POr(_, span) -> span
    PAs(_, _, span) -> span
  }
}
