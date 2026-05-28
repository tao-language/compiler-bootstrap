/// Core Abstract Syntax Tree
///
/// The core language is language-agnostic. It defines the fundamental
/// terms and values that make up the compiler's internal representation.
///
/// Terms use De Bruijn **indices** for variables. Values use De Bruijn
/// **levels** for runtime representation.
///
/// De Bruijn **indices** (Term `Var(n)`): relative to binders. `Var(0)` is
/// the innermost binder, `Var(1)` is the next one out, etc.
///
/// De Bruijn **levels** (Value `HVar(n)`): absolute positions in the
/// environment (`state.vars`). Level 0 is the most-recently-pushed entry
/// (innermost binder), level 1 is the next, etc.
///
/// Because `state.vars` is ordered innermost-first (see `state.gleam`),
/// levels and indices use the **same** counting convention:
///   level 0 = index 0 = innermost binder
///   level 1 = index 1 = next binder out
///   ...
/// This means quoting a level to an index is the identity conversion.
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
  Lam(implicit: Bool, param: #(String, Term), body: Term, span: Span)
  Pi(implicit: Bool, domain: #(String, Term), codomain: Term, span: Span)
  Fix(name: String, body: Term, span: Span)
  App(fun: Term, arg: Term, span: Span)
  Union(
    variants: List(#(String, #(List(String), Term, Term), Span)),
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
// VALUES (Semantics level - De Bruijn levels)
// ============================================================================

/// Core values - normalized terms after evaluation.
///
/// Values use De Bruijn levels for variables (relative to their
/// binding site), and De Bruijn indices for bodies.
pub type Value {
  VTyp(universe: Int)
  VLit(literal: Literal)
  VLitT(literal: LiteralType)
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
  VRcdT(fields: List(#(String, Value, Option(Value))))
  VNeut(neutral: Neut)
  VLam(implicit: Bool, param: #(String, Value), body: #(Env, Term))
  VPi(implicit: Bool, domain: #(String, Value), codomain: #(Env, Term))
  VFix(name: String, body: #(Env, Term))
  VUnion(variants: List(#(String, #(List(String), Value, Term))))
  VErr
}

pub type Neut {
  NVar(level: Int)
  NHole(id: Int)
  NApp(fun: Neut, arg: Value)
  NFixApp(name: String, body: #(Env, Term), arg: Neut)
  NMatch(env: Env, arg: Neut, cases: List(Case))
  NCall(name: String, args: List(Value))
}

// ============================================================================
// AST TERMS (Syntax level - Named variables, before De Bruijn conversion)
// ============================================================================

/// Named terms - AST produced by the parser with named variables.
///
/// Variables use names instead of De Bruijn indices. A separate conversion
/// pass (term_to_debruijn) converts NamedTerm to Term, calculating
/// De Bruijn indices and desugaring syntax sugar like $let.
///
/// This separates parsing from index calculation, making both simpler.
pub type AST {
  ATyp(universe: Int, span: Span)
  AHole(id: Int, span: Span)
  ALit(value: Literal, span: Span)
  ALitT(t: LiteralType, span: Span)
  AVar(name: String, span: Span)
  ACtr(tag: String, arg: AST, span: Span)
  ARcd(fields: List(#(String, AST)), span: Span)
  ARcdT(fields: List(#(String, AST, Option(AST))), span: Span)
  ACall(name: String, args: List(#(AST, AST)), return_type: AST, span: Span)
  AAnn(term: AST, type_: AST, span: Span)
  ALam(
    implicits: List(#(String, AST)),
    param: #(String, AST),
    body: AST,
    span: Span,
  )
  APi(
    implicits: List(#(String, AST)),
    domain: #(String, AST),
    codomain: AST,
    span: Span,
  )
  AFix(name: String, body: AST, span: Span)
  AApp(fun: AST, arg: AST, span: Span)
  ATypeDef(
    params: List(#(String, AST)),
    constructors: List(#(String, #(List(String), AST, AST), Span)),
    span: Span,
  )
  AMatch(arg: AST, cases: List(ACase), span: Span)
  AErr(message: String, span: Span)
  /// Syntax sugar: `let name = value; body`
  /// Desugars to App(Lam([], (name, param_type), body), value)
  ALet(name: String, param_type: AST, value: AST, body: AST, span: Span)
}

pub type ACase {
  ACase(pattern: Pattern, guard: Option(#(AST, Pattern)), body: AST, span: Span)
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
    Union(span: span, ..) -> span
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

pub fn vvar(level: Int) -> Value {
  VNeut(NVar(level))
}

pub fn vhole(id: Int) -> Value {
  VNeut(NHole(id))
}

pub fn vapp(fun: Neut, arg: Value) -> Value {
  VNeut(NApp(fun, arg))
}

pub fn vfix_app(name: String, body: #(Env, Term), arg: Neut) -> Value {
  VNeut(NFixApp(name, body, arg))
}

pub fn vcall(name: String, args: List(Value)) -> Value {
  VNeut(NCall(name, args))
}

pub fn vmatch(env: Env, arg: Neut, cases: List(Case)) -> Value {
  VNeut(NMatch(env, arg, cases))
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
