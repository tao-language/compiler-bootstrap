import core/literals.{type Literal, type LiteralType} as lit
import gleam/list
import gleam/option.{type Option, None, Some}
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
pub type Term {
  Term(data: TermData, span: Span)
}

pub type Type =
  Term

pub type TermData {
  Typ(universe: Int)
  Hole(id: Option(Int))
  Lit(value: Literal)
  LitT(t: LiteralType)
  Var(name: String)
  Ctr(tag: String, arg: Term)
  Rcd(fields: List(#(String, Term)))
  RcdT(fields: List(#(String, #(Option(Term), Option(Term)))))
  Ann(term: Term, type_: Type)
  Lam(implicit: Bool, param: Param, body: Term)
  Pi(implicit: Bool, param: Param, body: Term)
  Fix(name: String, body: Term)
  App(implicit: Bool, fun: Term, arg: Term)
  Match(arg: Term, cases: List(Case))
  Call(name: String, returns: Type, args: List(Term))
  TypeDef(type_def: TypeDefinition)
  Err
}

pub type Param =
  #(String, Option(Type))

pub type Pattern {
  Pattern(data: PatternData, span: Span)
}

pub type PatternData {
  PAny
  PTyp(universe: Int)
  PLit(value: Literal)
  PLitT(lit_type: LiteralType)
  PAlias(pattern: Pattern, name: String)
  PCtr(tag: String, pattern: Pattern)
  PRcd(fields: List(#(String, Pattern)))
  PRcdT(fields: List(#(String, Pattern)))
  PErr
}

pub type Case {
  Case(pattern: Pattern, guard: Option(#(Term, Pattern)), body: Term)
}

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, Term)),
    arg: Term,
    variants: List(#(String, Variant)),
  )
}

pub type Variant {
  Variant(params: List(#(String, Term)), arg: Term, returns: Term)
}

// Syntax sugar

pub fn typ(universe: Int, span: Span) {
  Term(Typ(universe), span)
}

pub fn hole(id: Option(Int), span: Span) {
  Term(Hole(id), span)
}

pub fn int(value: Int, span: Span) {
  Term(Lit(lit.Int(value)), span)
}

pub fn float(value: Float, span: Span) {
  Term(Lit(lit.Float(value)), span)
}

pub fn int_t(span: Span) {
  Term(LitT(lit.IntT), span)
}

pub fn float_t(span: Span) {
  Term(LitT(lit.FloatT), span)
}

pub fn i8(span: Span) {
  Term(LitT(lit.I8), span)
}

pub fn i16(span: Span) {
  Term(LitT(lit.I16), span)
}

pub fn i32(span: Span) {
  Term(LitT(lit.I32), span)
}

pub fn i64(span: Span) {
  Term(LitT(lit.I64), span)
}

pub fn u8(span: Span) {
  Term(LitT(lit.U8), span)
}

pub fn u16(span: Span) {
  Term(LitT(lit.U16), span)
}

pub fn u32(span: Span) {
  Term(LitT(lit.U32), span)
}

pub fn u64(span: Span) {
  Term(LitT(lit.U64), span)
}

pub fn f16(span: Span) {
  Term(LitT(lit.F16), span)
}

pub fn f32(span: Span) {
  Term(LitT(lit.F32), span)
}

pub fn f64(span: Span) {
  Term(LitT(lit.F64), span)
}

pub fn var(name: String, span: Span) {
  Term(Var(name), span)
}

pub fn ctr(tag: String, arg: Term, span: Span) {
  Term(Ctr(tag, arg), span)
}

pub fn rcd(fields: List(#(String, Term)), span: Span) {
  Term(Rcd(fields), span)
}

pub fn rcd_t(
  fields: List(#(String, #(Option(Type), Option(Term)))),
  span: Span,
) {
  Term(RcdT(fields), span)
}

pub fn ann(value: Term, type_: Term, span: Span) {
  Term(Ann(value, type_), span)
}

pub fn lam(param: Param, body: Term, span: Span) {
  Term(Lam(False, param, body), span)
}

pub fn lam_implicit(param: Param, body: Term, span: Span) {
  Term(Lam(True, param, body), span)
}

pub fn fun(
  param_name: String,
  args: List(#(String, #(Option(Term), Option(Term)))),
  args_span: Span,
  body: Term,
  span: Span,
) {
  let param = #(param_name, Some(rcd_t(args, args_span)))
  let pvars =
    list.map(args, fn(arg) {
      let #(name, _) = arg
      // TODO: add span to arg name and get it from there
      #(name, pvar(name, span))
    })
  let body =
    match(
      var(param_name, args_span),
      [Case(prcd(pvars, args_span), None, body)],
      span,
    )
  lam(param, body, span)
}

pub fn pi(param: Param, body: Term, span: Span) {
  Term(Pi(False, param, body), span)
}

pub fn pi_implicit(param: Param, body: Term, span: Span) {
  Term(Pi(True, param, body), span)
}

pub fn fix(name: String, body: Term, span: Span) {
  Term(Fix(name, body), span)
}

pub fn app(fun: Term, arg: Term, span: Span) {
  Term(App(False, fun, arg), span)
}

pub fn app_implicit(fun: Term, arg: Term, span: Span) {
  Term(App(True, fun, arg), span)
}

pub fn match(arg: Term, cases: List(Case), span: Span) {
  Term(Match(arg, cases), span)
}

pub fn call(name: String, returns: Type, args: List(Term), span: Span) {
  Term(Call(name, returns, args), span)
}

pub fn let_var(def: #(String, Option(Type), Term), body: Term, span: Span) {
  let #(name, opt_type, value) = def
  app(lam(#(name, opt_type), body, span), value, span)
}

pub fn let_pat(def: #(Pattern, Option(Type), Term), body: Term, span: Span) {
  let #(pattern, opt_type, value) = def
  let body = case opt_type {
    Some(type_) -> ann(body, type_, type_.span)
    None -> body
  }
  match(value, [Case(pattern, None, body)], span)
}

pub fn err(span: Span) {
  Term(Err, span)
}

pub fn pany(span: Span) {
  Pattern(PAny, span)
}

pub fn pvar(name: String, span: Span) {
  palias(pany(span), name, span)
}

pub fn pint(value: Int, span: Span) {
  Pattern(PLit(lit.Int(value)), span)
}

pub fn pfloat(value: Float, span: Span) {
  Pattern(PLit(lit.Float(value)), span)
}

pub fn prcd(fields: List(#(String, Pattern)), span: Span) {
  Pattern(PRcd(fields), span)
}

pub fn prcd_t(fields: List(#(String, Pattern)), span: Span) {
  Pattern(PRcdT(fields), span)
}

pub fn pctr(tag: String, arg: Pattern, span: Span) {
  Pattern(PCtr(tag, arg), span)
}

pub fn palias(pattern: Pattern, name: String, span: Span) {
  Pattern(PAlias(pattern, name), span)
}
