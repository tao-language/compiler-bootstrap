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
  Expr(data: ExprData, span: Span, trace: Option(String))
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
  Rcd(
    fields: List(#(String, #(Option(Expr), Option(Expr)))),
    tail: Option(Expr),
  )
  Ann(term: Expr, type_: Type)
  For(param: Param, body: Expr)
  Lam(param: Param, body: Expr)
  Pi(param: Param, body: Expr)
  Fix(name: String, body: Expr)
  App(fun: Expr, arg: Expr)
  Match(arg: Expr, cases: List(Case))
  Call(name: String, arg: Expr)
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
  PRcd(fields: List(#(String, Pattern)), tail: Option(Pattern))
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
    PRcd(fields, opt_tail) -> {
      let xs =
        list.flat_map(fields, fn(field) {
          let #(x, pattern) = field
          [x, ..bindings(pattern)]
        })
      let ys = case opt_tail {
        Some(tail) -> bindings(tail)
        None -> []
      }
      list.append(xs, ys)
    }
    _ -> []
  }
}

pub fn contains(term: Expr, name: String) -> Bool {
  case term.data {
    Var(x) if x == name -> True
    Ctr(_, arg) -> contains(arg, name)
    Rcd(fields, opt_tail) ->
      list.any(fields, fn(field) {
        let #(_, #(opt_type, opt_default)) = field
        opt_contains(opt_type, name) || opt_contains(opt_default, name)
      })
      || opt_contains(opt_tail, name)
    Ann(term, type_) -> contains(term, name) || contains(type_, name)
    For(#(x, type_), body) ->
      opt_contains(type_, name) || x != name && contains(body, name)
    Lam(#(x, type_), body) ->
      opt_contains(type_, name) || x != name && contains(body, name)
    Pi(#(x, type_), body) ->
      opt_contains(type_, name) || x != name && contains(body, name)
    Fix(x, body) if x != name -> contains(body, name)
    App(fun, arg) -> contains(fun, name) || contains(arg, name)
    Match(arg, cases) ->
      contains(arg, name) || list.any(cases, contains_case(_, name))
    Call(_, arg) -> contains(arg, name)
    TypeDef(type_def) -> todo
    _ -> False
  }
}

fn contains_case(c: Case, name: String) -> Bool {
  !list.contains(bindings(c.pattern), name)
  && contains_case_body(c.guard, c.body, name)
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
  Expr(Typ(universe), span, None)
}

pub fn hole(id: Option(Int), span: Span) {
  Expr(Hole(id), span, None)
}

pub fn lit(k: Literal, span: Span) {
  Expr(Lit(k), span, None)
}

pub fn int(value: Int, span: Span) {
  Expr(Lit(lit.Int(value)), span, None)
}

pub fn float(value: Float, span: Span) {
  Expr(Lit(lit.Float(value)), span, None)
}

pub fn lit_t(k: LiteralType, span: Span) {
  Expr(LitT(k), span, None)
}

pub fn int_t(span: Span) {
  Expr(LitT(lit.IntT), span, None)
}

pub fn float_t(span: Span) {
  Expr(LitT(lit.FloatT), span, None)
}

pub fn i8(span: Span) {
  Expr(LitT(lit.I8), span, None)
}

pub fn i16(span: Span) {
  Expr(LitT(lit.I16), span, None)
}

pub fn i32(span: Span) {
  Expr(LitT(lit.I32), span, None)
}

pub fn i64(span: Span) {
  Expr(LitT(lit.I64), span, None)
}

pub fn u8(span: Span) {
  Expr(LitT(lit.U8), span, None)
}

pub fn u16(span: Span) {
  Expr(LitT(lit.U16), span, None)
}

pub fn u32(span: Span) {
  Expr(LitT(lit.U32), span, None)
}

pub fn u64(span: Span) {
  Expr(LitT(lit.U64), span, None)
}

pub fn f16(span: Span) {
  Expr(LitT(lit.F16), span, None)
}

pub fn f32(span: Span) {
  Expr(LitT(lit.F32), span, None)
}

pub fn f64(span: Span) {
  Expr(LitT(lit.F64), span, None)
}

pub fn var(name: String, span: Span) {
  Expr(Var(name), span, None)
}

pub fn ctr(tag: String, arg: Expr, span: Span) {
  Expr(Ctr(tag, arg), span, None)
}

pub fn ctr_args(tag: String, args: List(#(String, Expr)), span: Span) {
  ctr(tag, rcd_values(args, None, span), span)
}

pub fn ctr0(tag: String, span: Span) {
  ctr_args(tag, [], span)
}

pub fn rcd(
  fields: List(#(String, #(Option(Type), Option(Expr)))),
  tail: Option(Expr),
  span: Span,
) {
  Expr(Rcd(fields, tail), span, None)
}

pub fn rcd_values(
  fields: List(#(String, Expr)),
  tail: Option(Expr),
  span: Span,
) {
  let fields =
    list.map(fields, fn(field) {
      let #(name, value) = field
      #(name, #(Some(value), None))
    })
  rcd(fields, tail, span)
}

pub fn rcd_vars(vars: List(String), tail: Option(Expr), span: Span) {
  let fields = list.map(vars, fn(name) { #(name, var(name, span)) })
  rcd_values(fields, tail, span)
}

pub fn ann(value: Expr, type_: Expr, span: Span) {
  Expr(Ann(value, type_), span, None)
}

pub fn for(param: Param, body: Expr, span: Span) {
  Expr(For(param, body), span, None)
}

pub fn lam(param: Param, body: Expr, span: Span) {
  Expr(Lam(param, body), span, None)
}

pub fn pi(param: Param, body: Expr, span: Span) {
  Expr(Pi(param, body), span, None)
}

pub fn fix(name: String, body: Expr, span: Span) {
  case contains(body, name) {
    True -> Expr(Fix(name, body), span, None)
    False -> body
  }
}

pub fn fix_strict(name: String, body: Expr, span: Span) {
  Expr(Fix(name, body), span, None)
}

pub fn app(fun: Expr, arg: Expr, span: Span) {
  Expr(App(fun, arg), span, None)
}

pub fn match(arg: Expr, cases: List(Case), span: Span) {
  Expr(Match(arg, cases), span, None)
}

pub fn call(name: String, arg: Expr, span: Span) {
  Expr(Call(name, arg), span, None)
}

pub fn call_args(name: String, args: List(#(String, Expr)), span: Span) {
  call(name, rcd_values(args, None, span), span)
}

pub fn call0(name: String, span: Span) {
  call_args(name, [], span)
}

pub fn let_var(def: #(String, Option(Type), Expr), body: Expr, span: Span) {
  let_var_trace(def, body, span, None)
}

pub fn let_var_trace(
  def: #(String, Option(Type), Expr),
  body: Expr,
  span: Span,
  trace: Option(String),
) {
  let #(name, opt_type, value) = def
  Expr(App(lam(#(name, opt_type), body, span), value), span, trace)
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

pub fn let_pat_trace(
  def: #(Pattern, Option(Type), Expr),
  body: Expr,
  span: Span,
  trace: Option(String),
) {
  let #(pattern, opt_type, value) = def
  case pattern.data {
    PAlias(Pattern(PAny, _), name) ->
      let_var_trace(#(name, opt_type, value), body, span, trace)
    _ -> {
      let body = case opt_type {
        Some(type_) -> ann(body, type_, type_.span)
        None -> body
      }
      Expr(Match(value, [Case(pattern, None, body)]), span, trace)
    }
  }
}

pub fn dot(expr: Expr, field: String, span: Span) {
  dot_trace(expr, field, span, None)
}

pub fn dot_trace(expr: Expr, field: String, span: Span, trace: Option(String)) {
  let pattern = prcd([#(field, pvar(field, span))], Some(pany(span)), span)
  let body = var(field, span)
  Expr(Match(expr, [Case(pattern, None, body)]), span, trace)
}

pub fn err(span: Span) {
  Expr(Err, span, None)
}

pub fn pany(span: Span) {
  Pattern(PAny, span)
}

pub fn ptyp(universe: Int, span: Span) {
  Pattern(PTyp(universe), span)
}

pub fn pvar(name: String, span: Span) {
  palias(pany(span), name, span)
}

pub fn plit(k: Literal, span: Span) {
  Pattern(PLit(k), span)
}

pub fn pint(value: Int, span: Span) {
  Pattern(PLit(lit.Int(value)), span)
}

pub fn pfloat(value: Float, span: Span) {
  Pattern(PLit(lit.Float(value)), span)
}

pub fn plit_t(k: LiteralType, span: Span) {
  Pattern(PLitT(k), span)
}

pub fn pint_t(span: Span) {
  Pattern(PLitT(lit.IntT), span)
}

pub fn pfloat_t(span: Span) {
  Pattern(PLitT(lit.FloatT), span)
}

pub fn pi8(span: Span) {
  Pattern(PLitT(lit.I8), span)
}

pub fn pi16(span: Span) {
  Pattern(PLitT(lit.I16), span)
}

pub fn pi32(span: Span) {
  Pattern(PLitT(lit.I32), span)
}

pub fn pi64(span: Span) {
  Pattern(PLitT(lit.I64), span)
}

pub fn pu8(span: Span) {
  Pattern(PLitT(lit.U8), span)
}

pub fn pu16(span: Span) {
  Pattern(PLitT(lit.U16), span)
}

pub fn pu32(span: Span) {
  Pattern(PLitT(lit.U32), span)
}

pub fn pu64(span: Span) {
  Pattern(PLitT(lit.U64), span)
}

pub fn pf16(span: Span) {
  Pattern(PLitT(lit.F16), span)
}

pub fn pf32(span: Span) {
  Pattern(PLitT(lit.F32), span)
}

pub fn pf64(span: Span) {
  Pattern(PLitT(lit.F64), span)
}

pub fn prcd(
  fields: List(#(String, Pattern)),
  tail: Option(Pattern),
  span: Span,
) {
  Pattern(PRcd(fields, tail), span)
}

pub fn pctr(tag: String, arg: Pattern, span: Span) {
  Pattern(PCtr(tag, arg), span)
}

pub fn pctr_args(tag: String, args: List(#(String, Pattern)), span: Span) {
  pctr(tag, prcd(args, None, span), span)
}

pub fn pctr0(tag: String, span: Span) {
  pctr_args(tag, [], span)
}

pub fn palias(pattern: Pattern, name: String, span: Span) {
  Pattern(PAlias(pattern, name), span)
}
