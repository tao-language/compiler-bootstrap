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
pub type Expr {
  Expr(data: ExprData, span: Span)
}

pub type Type =
  Expr

pub type ExprData {
  Typ(universe: Int)
  Hole(id: Option(Int))
  Lit(value: Literal)
  LitT(t: LiteralType)
  Var(name: String)
  Ctr(tag: String, arg: Expr)
  Rcd(fields: List(#(String, Expr)))
  RcdT(fields: List(#(String, #(Option(Expr), Option(Expr)))))
  Ann(term: Expr, type_: Type)
  Lam(implicit: Bool, param: Param, body: Expr)
  Pi(implicit: Bool, param: Param, body: Expr)
  Fix(name: String, body: Expr)
  App(implicit: Bool, fun: Expr, arg: Expr)
  Match(arg: Expr, cases: List(Case))
  Call(name: String, returns: Type, args: List(Expr))
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
  Case(pattern: Pattern, guard: Option(#(Expr, Pattern)), body: Expr)
}

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, Expr)),
    arg: Expr,
    variants: List(#(String, Variant)),
  )
}

pub type Variant {
  Variant(params: List(#(String, Expr)), arg: Expr, returns: Expr)
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

pub fn contains(term: Expr, name: String) -> Bool {
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
  guard: Option(#(Expr, Pattern)),
  body: Expr,
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

fn opt_contains(opt_term: Option(Expr), name: String) -> Bool {
  case opt_term {
    Some(term) -> contains(term, name)
    None -> False
  }
}

// Syntax sugar

pub fn typ(universe: Int, span: Span) {
  Expr(Typ(universe), span)
}

pub fn hole(id: Option(Int), span: Span) {
  Expr(Hole(id), span)
}

pub fn int(value: Int, span: Span) {
  Expr(Lit(lit.Int(value)), span)
}

pub fn float(value: Float, span: Span) {
  Expr(Lit(lit.Float(value)), span)
}

pub fn int_t(span: Span) {
  Expr(LitT(lit.IntT), span)
}

pub fn float_t(span: Span) {
  Expr(LitT(lit.FloatT), span)
}

pub fn i8(span: Span) {
  Expr(LitT(lit.I8), span)
}

pub fn i16(span: Span) {
  Expr(LitT(lit.I16), span)
}

pub fn i32(span: Span) {
  Expr(LitT(lit.I32), span)
}

pub fn i64(span: Span) {
  Expr(LitT(lit.I64), span)
}

pub fn u8(span: Span) {
  Expr(LitT(lit.U8), span)
}

pub fn u16(span: Span) {
  Expr(LitT(lit.U16), span)
}

pub fn u32(span: Span) {
  Expr(LitT(lit.U32), span)
}

pub fn u64(span: Span) {
  Expr(LitT(lit.U64), span)
}

pub fn f16(span: Span) {
  Expr(LitT(lit.F16), span)
}

pub fn f32(span: Span) {
  Expr(LitT(lit.F32), span)
}

pub fn f64(span: Span) {
  Expr(LitT(lit.F64), span)
}

pub fn var(name: String, span: Span) {
  Expr(Var(name), span)
}

pub fn ctr(tag: String, arg: Expr, span: Span) {
  Expr(Ctr(tag, arg), span)
}

pub fn rcd(fields: List(#(String, Expr)), span: Span) {
  Expr(Rcd(fields), span)
}

pub fn rcd_vars(vars: List(String), span: Span) {
  rcd(list.map(vars, fn(name) { #(name, var(name, span)) }), span)
}

pub fn rcd_t(
  fields: List(#(String, #(Option(Type), Option(Expr)))),
  span: Span,
) {
  Expr(RcdT(fields), span)
}

pub fn ann(value: Expr, type_: Expr, span: Span) {
  Expr(Ann(value, type_), span)
}

pub fn lam(param: Param, body: Expr, span: Span) {
  Expr(Lam(False, param, body), span)
}

pub fn lam_implicit(param: Param, body: Expr, span: Span) {
  Expr(Lam(True, param, body), span)
}

pub fn pi(param: Param, body: Expr, span: Span) {
  Expr(Pi(False, param, body), span)
}

pub fn pi_implicit(param: Param, body: Expr, span: Span) {
  Expr(Pi(True, param, body), span)
}

pub fn fix(name: String, body: Expr, span: Span) {
  case contains(body, name) {
    True -> Expr(Fix(name, body), span)
    False -> body
  }
}

pub fn app(fun: Expr, arg: Expr, span: Span) {
  Expr(App(False, fun, arg), span)
}

pub fn app_implicit(fun: Expr, arg: Expr, span: Span) {
  Expr(App(True, fun, arg), span)
}

pub fn match(arg: Expr, cases: List(Case), span: Span) {
  Expr(Match(arg, cases), span)
}

pub fn call(name: String, returns: Type, args: List(Expr), span: Span) {
  Expr(Call(name, returns, args), span)
}

pub fn let_var(def: #(String, Option(Type), Expr), body: Expr, span: Span) {
  let #(name, opt_type, value) = def
  app(lam(#(name, opt_type), body, span), value, span)
}

pub fn let_pat(def: #(Pattern, Option(Type), Expr), body: Expr, span: Span) {
  let #(pattern, opt_type, value) = def
  case pattern.data {
    PAlias(Pattern(PAny, _), name) ->
      let_var(#(name, opt_type, value), body, span)
    _ -> {
      let body = case opt_type {
        Some(type_) -> ann(body, type_, type_.span)
        None -> body
      }
      match(value, [Case(pattern, None, body)], span)
    }
  }
}

pub fn dot(expr: Expr, field: String, span: Span) {
  let pattern = prcd([#(field, pvar(field, span))], span)
  let body = var(field, span)
  match(expr, [Case(pattern, None, body)], span)
}

pub fn err(span: Span) {
  Expr(Err, span)
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
