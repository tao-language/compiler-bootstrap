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

// Helper functions

pub fn bindings(pattern: Pattern) -> List(String) {
  case pattern.data {
    PAlias(pattern, x) -> [x, ..bindings(pattern)]
    PCtr(_, pattern) -> bindings(pattern)
    PRcd(fields) ->
      list.flat_map(fields, fn(field) {
        let #(x, pattern) = field
        [x, ..bindings(pattern)]
      })
    PRcdT(fields) ->
      list.flat_map(fields, fn(field) {
        let #(x, pattern) = field
        [x, ..bindings(pattern)]
      })
    _ -> []
  }
}

pub fn contains(term: Term, name: String) -> Bool {
  case term.data {
    Var(x) if x == name -> True
    Ctr(_, arg) -> contains(arg, name)
    Rcd(fields) ->
      list.any(fields, fn(field) {
        let #(_, term) = field
        contains(term, name)
      })
    RcdT(fields) ->
      list.any(fields, fn(field) {
        let #(_, #(opt_type, opt_default)) = field
        opt_contains(opt_type, name) || opt_contains(opt_default, name)
      })
    Ann(term, type_) -> contains(term, name) || contains(type_, name)
    Lam(_, #(x, type_), body) ->
      opt_contains(type_, name) || x != name && contains(body, name)
    Pi(_, #(x, type_), body) ->
      opt_contains(type_, name) || x != name && contains(body, name)
    Fix(x, body) if x != name -> contains(body, name)
    App(_, fun, arg) -> contains(fun, name) || contains(arg, name)
    Match(arg, cases) ->
      contains(arg, name) || list.any(cases, contains_case(_, name))
    Call(name, returns, args) -> todo
    TypeDef(type_def) -> todo
    _ -> False
  }
}

fn contains_case(c: Case, name: String) -> Bool {
  !list.contains(bindings(c.pattern), name)
  || contains_case_body(c.guard, c.body, name)
}

fn contains_case_body(
  guard: Option(#(Term, Pattern)),
  body: Term,
  name: String,
) -> Bool {
  case guard {
    Some(#(term, pattern)) ->
      contains(term, name)
      || !list.contains(bindings(pattern), name)
      && contains(body, name)
    None -> contains(body, name)
  }
}

fn opt_contains(opt_term: Option(Term), name: String) -> Bool {
  case opt_term {
    Some(term) -> contains(term, name)
    None -> False
  }
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
  case contains(body, name) {
    True -> Term(Fix(name, body), span)
    False -> body
  }
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
