import core/literals.{type Literal, type LiteralType} as lit
import gleam/option.{type Option}
import syntax/span.{type Span}

// ============================================================================
// AST TERMS (Syntax level - Named variables, before De Bruijn conversion)
// ============================================================================

/// Named terms - AST produced by the parser with named variables.
///
/// Variables use names instead of De Bruijn indices. A separate conversion
/// pass (term_to_debruijn) converts NamedTerm to Term, calculating
/// De Bruijn indices and desugaring syntax sugar like %let.
///
/// This separates parsing from index calculation, making both simpler.
pub type AST {
  AST(data: Data, span: Span)
}

pub type Data {
  Typ(universe: Int)
  Hole(id: Int)
  Lit(value: Literal)
  LitT(t: LiteralType)
  Var(name: String)
  Ctr(tag: String, arg: AST)
  Rcd(fields: List(#(String, AST)))
  RcdT(fields: List(#(String, #(AST, Option(AST)))))
  Ann(term: AST, type_: AST)
  Lam(implicit: Bool, param: #(String, AST), body: AST)
  Pi(implicit: Bool, domain: #(String, AST), codomain: AST)
  Fix(name: String, body: AST)
  App(implicit: Bool, fun: AST, arg: AST)
  TypeDef(type_def: TypeDefinition)
  Let(name: String, param_type: AST, value: AST, body: AST)
  Match(arg: AST, cases: List(Case))
  Call(name: String, args: List(AST), return_type: AST)
  Err
}

pub type Pattern {
  PAny(span: Span)
  PTyp(universe: Int, span: Span)
  PLit(value: Literal, span: Span)
  PLitT(lit_type: LiteralType, span: Span)
  PAlias(name: String, pattern: Pattern, span: Span)
  PCtr(tag: String, pattern: Pattern, span: Span)
  PRcd(fields: List(#(String, Pattern)), span: Span)
  PErr(span: Span)
}

pub type Case {
  Case(pattern: Pattern, guard: Option(#(AST, Pattern)), body: AST, span: Span)
}

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, AST)),
    arg: AST,
    variants: List(#(String, Variant)),
  )
}

pub type Variant {
  Variant(params: List(#(String, AST)), arg: AST, return_type: AST)
}

// Helper functions

pub fn pattern_span(pattern: Pattern) -> Span {
  case pattern {
    PAny(span) -> span
    PTyp(_, span) -> span
    PLit(_, span) -> span
    PLitT(_, span) -> span
    PAlias(_, _, span) -> span
    PCtr(_, _, span) -> span
    PRcd(_, span) -> span
    PErr(span) -> span
  }
}

// Syntax sugar

pub fn typ(universe: Int, span: Span) -> AST {
  AST(Typ(universe), span)
}

pub fn hole(id: Int, span: Span) -> AST {
  AST(Hole(id), span)
}

pub fn int(value: Int, span: Span) -> AST {
  AST(Lit(lit.Int(value)), span)
}

pub fn float(value: Float, span: Span) -> AST {
  AST(Lit(lit.Float(value)), span)
}

pub fn int_t(span: Span) {
  AST(LitT(lit.IntT), span)
}

pub fn float_t(span: Span) {
  AST(LitT(lit.FloatT), span)
}

pub fn i8(span: Span) {
  AST(LitT(lit.I8), span)
}

pub fn i16(span: Span) {
  AST(LitT(lit.I16), span)
}

pub fn i32(span: Span) {
  AST(LitT(lit.I32), span)
}

pub fn i64(span: Span) {
  AST(LitT(lit.I64), span)
}

pub fn u8(span: Span) {
  AST(LitT(lit.U8), span)
}

pub fn u16(span: Span) {
  AST(LitT(lit.U16), span)
}

pub fn u32(span: Span) {
  AST(LitT(lit.U32), span)
}

pub fn u64(span: Span) {
  AST(LitT(lit.U64), span)
}

pub fn f16(span: Span) {
  AST(LitT(lit.F16), span)
}

pub fn f32(span: Span) {
  AST(LitT(lit.F32), span)
}

pub fn f64(span: Span) {
  AST(LitT(lit.F64), span)
}

pub fn var(name: String, span: Span) {
  AST(Var(name), span)
}

pub fn ctr(tag: String, args: List(#(String, AST)), span: Span) {
  AST(Ctr(tag, AST(Rcd(args), span)), span)
}

pub fn rcd(fields: List(#(String, AST)), span: Span) {
  AST(Rcd(fields), span)
}

pub fn rcd_t(fields: List(#(String, #(AST, Option(AST)))), span: Span) {
  AST(RcdT(fields), span)
}

pub fn ann(value: AST, type_: AST, span: Span) {
  AST(Ann(value, type_), span)
}

pub fn lam(param: #(String, AST), body: AST, span: Span) {
  AST(Lam(False, param, body), span)
}

pub fn lam_implicit(param: #(String, AST), body: AST, span: Span) {
  AST(Lam(True, param, body), span)
}

pub fn pi(param: #(String, AST), body: AST, span: Span) {
  AST(Pi(False, param, body), span)
}

pub fn pi_implicit(param: #(String, AST), body: AST, span: Span) {
  AST(Pi(True, param, body), span)
}

pub fn fix(name: String, body: AST, span: Span) {
  AST(Fix(name, body), span)
}

pub fn app(fun: AST, arg: AST, span: Span) {
  AST(App(False, fun, arg), span)
}

pub fn app_implicit(fun: AST, arg: AST, span: Span) {
  AST(App(True, fun, arg), span)
}

pub fn match(arg: AST, cases: List(Case), span: Span) {
  AST(Match(arg, cases), span)
}

pub fn call(name: String, args: List(AST), return_type: AST, span: Span) {
  AST(Call(name, args, return_type), span)
}

pub fn err(span: Span) {
  AST(Err, span)
}

/// Syntax sugar for `_@name`.
pub fn pvar(name: String, span: Span) -> Pattern {
  PAlias(name, PAny(span), span)
}

pub fn pint(value: Int, span: Span) -> Pattern {
  PLit(lit.Int(value), span)
}

pub fn pfloat(value: Float, span: Span) -> Pattern {
  PLit(lit.Float(value), span)
}
