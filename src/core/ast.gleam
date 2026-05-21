/// Core Abstract Syntax Tree
///
/// The core language is language-agnostic. It defines the fundamental
/// terms and values that make up the compiler's internal representation.
///
/// Terms use De Bruijn indices for variables. Values use De Bruijn
/// levels for runtime representation.
import gleam/option.{type Option}
import syntax/span.{type Span}

// ============================================================================
// LITERALS
// ============================================================================

pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

pub type LiteralType {
  IntT
  FloatT
  I8
  I16
  I32
  I64
  U8
  U16
  U32
  U64
  F16
  F32
  F64
}

// ============================================================================
// TERMS (Syntax level - De Bruijn indices)
// ============================================================================

/// Core terms. The AST for type checking and evaluation.
///
/// Terms use De Bruijn indices: Var(0) refers to the innermost
/// enclosing binder, Var(1) to the one before that, etc.
pub type Term {
  Typ(universe: Int, span: Span)
  Hole(id: Int, span: Span)
  Lit(value: Literal, span: Span)
  LitT(typ: LiteralType, span: Span)
  Var(index: Int, span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Rcd(fields: List(#(String, Term)), span: Span)
  RcdT(fields: List(#(String, Term, Option(Term))), span: Span)
  Call(name: String, args: List(Term), return_type: Term, span: Span)
  Ann(term: Term, type_: Term, span: Span)
  Lam(
    implicits: List(#(String, Term)),
    param: #(String, Term),
    body: Term,
    span: Span,
  )
  Pi(
    implicits: List(#(String, Term)),
    domain: #(String, Term),
    codomain: Term,
    span: Span,
  )
  Fix(name: String, body: Term, span: Span)
  App(fun: Term, arg: Term, span: Span)
  TypeDef(
    params: List(#(String, Term)),
    constructors: List(#(String, #(List(String), Term, Term), Span)),
    span: Span,
  )
  Match(arg: Term, cases: List(Case), span: Span)
  Err(span: Span)
}

pub type Pattern {
  PAny(span: Span)
  PTyp(universe: Int, span: Span)
  PLit(value: Literal, span: Span)
  PLitT(lit_type: LiteralType, span: Span)
  PAlias(name: String, pattern: Pattern, span: Span)
  PCtr(tag: String, pattern: Pattern, span: Span)
  PRcd(fields: List(#(String, Pattern)), span: Span)
  PError(span: Span)
}

pub type Case {
  Case(
    pattern: Pattern,
    guard: Option(#(Term, Pattern)),
    body: Term,
    span: Span,
  )
}

// ============================================================================
// NAMED TERMS (Syntax level - Named variables, before De Bruijn conversion)
// ============================================================================

/// Named terms - AST produced by the parser with named variables.
///
/// Variables use names instead of De Bruijn indices. A separate conversion
/// pass (term_to_debruijn) converts NamedTerm to Term, calculating
/// De Bruijn indices and desugaring syntax sugar like $let.
///
/// This separates parsing from index calculation, making both simpler.
pub type NamedTerm {
  NamedTyp(universe: Int, span: Span)
  NamedHole(id: Int, span: Span)
  NamedLit(value: Literal, span: Span)
  NamedLitT(t: LiteralType, span: Span)
  NamedVar(name: String, span: Span)
  NamedCtr(tag: String, arg: NamedTerm, span: Span)
  NamedRcd(fields: List(#(String, NamedTerm)), span: Span)
  NamedRcdT(fields: List(#(String, NamedTerm, Option(NamedTerm))), span: Span)
  NamedCall(
    name: String,
    args: List(#(NamedTerm, NamedTerm)),
    return_type: NamedTerm,
    span: Span,
  )
  NamedAnn(term: NamedTerm, type_: NamedTerm, span: Span)
  NamedLam(
    implicits: List(#(String, NamedTerm)),
    param: #(String, NamedTerm),
    body: NamedTerm,
    span: Span,
  )
  NamedPi(
    implicits: List(#(String, NamedTerm)),
    domain: #(String, NamedTerm),
    codomain: NamedTerm,
    span: Span,
  )
  NamedFix(name: String, body: NamedTerm, span: Span)
  NamedApp(fun: NamedTerm, arg: NamedTerm, span: Span)
  NamedTypeDef(
    params: List(#(String, NamedTerm)),
    constructors: List(#(String, #(List(String), NamedTerm, NamedTerm), Span)),
    span: Span,
  )
  NamedMatch(arg: NamedTerm, cases: List(NamedCase), span: Span)
  NamedErr(message: String, span: Span)
  /// Syntax sugar: `let name = value; body`
  /// Desugars to App(Lam([], (name, param_type), body), value)
  NamedLet(
    name: String,
    param_type: NamedTerm,
    value: NamedTerm,
    body: NamedTerm,
    span: Span,
  )
}

pub type NamedCase {
  NamedCase(
    pattern: Pattern,
    guard: Option(#(NamedTerm, Pattern)),
    body: NamedTerm,
    span: Span,
  )
}

// ============================================================================
// VALUES (Semantics level - De Bruijn levels)
// ============================================================================

/// Neutral term head - the start of a neutral spine.
pub type Head {
  HVar(level: Int)
  HHole(id: Int)
  HCall(name: String, args: List(Value))
}

/// Eliminators form applied to a neutral term.
pub type Elim {
  EApp(arg: Value, span: Span)
  EFix(env: Env, body: Term)
  EMatch(env: Env, cases: List(Case), span: Span)
}

/// Core values - normalized terms after evaluation.
///
/// Values use De Bruijn levels for variables (relative to their
/// binding site), and De Bruijn indices for bodies.
pub type Value {
  VTyp(universe: Int)
  VLit(value: Literal)
  VLitT(t: LiteralType)
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
  VRcdT(fields: List(#(String, Value, Option(Value))))
  VNeut(head: Head, spine: List(Elim))
  VLam(
    env: Env,
    implicits: List(#(String, Value)),
    param: #(String, Value),
    body: Term,
  )
  VPi(
    env: Env,
    implicits: List(#(String, Value)),
    domain: #(String, Value),
    codomain: Term,
  )
  VTypeDef(
    params: List(#(String, Value)),
    constructors: List(#(String, #(List(String), Value, Term))),
  )
  VErr
}

pub type Env =
  List(Value)

pub fn get_span(term: Term) -> Span {
  case term {
    Typ(span: span, ..) -> span
    Hole(span: span, ..) -> span
    Lit(span: span, ..) -> span
    LitT(span: span, ..) -> span
    Var(span: span, ..) -> span
    Ctr(span: span, ..) -> span
    Rcd(span: span, ..) -> span
    RcdT(span: span, ..) -> span
    Call(span: span, ..) -> span
    TypeDef(span: span, ..) -> span
    Ann(span: span, ..) -> span
    Lam(span: span, ..) -> span
    Pi(span: span, ..) -> span
    Fix(span: span, ..) -> span
    App(span: span, ..) -> span
    Match(span: span, ..) -> span
    Err(span: span) -> span
  }
}

pub fn term_to_string(term: Term) -> String {
  todo
}

pub fn value_to_string(value: Value) -> String {
  todo
}

// SYNTAX SUGAR

/// Syntax sugar for `_@name`.
pub fn pvar(name: String, span: Span) -> Pattern {
  PAlias(name, PAny(span), span)
}

pub fn int(value: Int, span: Span) -> Term {
  Lit(Int(value), span)
}

pub fn float(value: Float, span: Span) -> Term {
  Lit(Float(value), span)
}

pub fn int_t(span: Span) -> Term {
  LitT(IntT, span)
}

pub fn float_t(span: Span) -> Term {
  LitT(FloatT, span)
}

pub fn i8(span: Span) -> Term {
  LitT(I8, span)
}

pub fn i16(span: Span) -> Term {
  LitT(I16, span)
}

pub fn i32(span: Span) -> Term {
  LitT(I32, span)
}

pub fn i64(span: Span) -> Term {
  LitT(I64, span)
}

pub fn u8(span: Span) -> Term {
  LitT(U8, span)
}

pub fn u16(span: Span) -> Term {
  LitT(U16, span)
}

pub fn u32(span: Span) -> Term {
  LitT(U32, span)
}

pub fn u64(span: Span) -> Term {
  LitT(U64, span)
}

pub fn f32(span: Span) -> Term {
  LitT(F32, span)
}

pub fn f64(span: Span) -> Term {
  LitT(F64, span)
}

pub fn vvar(level: Int, spine: List(Elim)) -> Value {
  VNeut(HVar(level), spine)
}

pub fn vhole(id: Int, spine: List(Elim)) -> Value {
  VNeut(HHole(id), spine)
}

pub fn vcall(name: String, args: List(Value), spine: List(Elim)) -> Value {
  VNeut(HCall(name, args), spine)
}

pub fn vint(value: Int) -> Value {
  VLit(Int(value))
}

pub fn vfloat(value: Float) -> Value {
  VLit(Float(value))
}

pub const vint_t = VLitT(IntT)

pub const vfloat_t = VLitT(FloatT)

pub const vi8 = VLitT(I8)

pub const vi16 = VLitT(I16)

pub const vi32 = VLitT(I32)

pub const vi64 = VLitT(I64)

pub const vu8 = VLitT(U8)

pub const vu16 = VLitT(U16)

pub const vu32 = VLitT(U32)

pub const vu64 = VLitT(U64)

pub const vf32 = VLitT(F32)

pub const vf64 = VLitT(F64)
