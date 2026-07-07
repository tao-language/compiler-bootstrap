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
import core/ast
import core/literals.{type Literal, type LiteralType} as lit
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span
import utils/list_utils.{list_at}

// ============================================================================
// TERMS (Syntax level - De Bruijn indices)
// ============================================================================

/// Core terms. The ast.Term for type checking and evaluation.
///
/// Terms use De Bruijn indices: Var(0) refers to the innermost
/// enclosing binder, Var(1) to the one before that, etc.
pub type Term {
  Typ(universe: Int)
  Hole(id: Int)
  Lit(value: Literal)
  LitT(typ: LiteralType)
  Var(index: Int)
  Ctr(tag: String, arg: Term)
  Rcd(fields: List(#(String, #(Term, Option(Term)))), tail: Option(Term))
  Call(name: String, returns: Type, args: List(Term))
  Ann(term: Term, type_: Type)
  Lam(implicit: Bool, param: #(String, Type), body: Term)
  Pi(implicit: Bool, domain: #(String, Type), codomain: Term)
  Fix(name: String, body: Term)
  App(implicit: Bool, fun: Term, arg: Term)
  Match(arg: Term, cases: List(Case))
  TypeDef(type_def: TypeDefinition)
  Err
}

pub type Type =
  Term

pub type Pattern {
  PAny
  PTyp(universe: Int)
  PLit(value: Literal)
  PLitT(lit_type: LiteralType)
  PAlias(name: String, pattern: Pattern)
  PCtr(tag: String, pattern: Pattern)
  PRcd(fields: List(#(String, Pattern)), tail: Option(Pattern))
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
  Variant(params: List(#(String, Term)), arg: Term, return_type: Term)
}

// Helper functions

pub fn pop_field(
  fields: List(#(String, a)),
  name: String,
) -> Option(#(a, List(#(String, a)))) {
  case fields {
    [] -> None
    [#("", value), ..fields] -> Some(#(value, fields))
    [#(key, value), ..fields] if name == "" || name == key ->
      Some(#(value, fields))
    [entry, ..fields] ->
      case pop_field(fields, name) {
        None -> None
        Some(#(value, fields)) -> Some(#(value, [entry, ..fields]))
      }
  }
}

pub fn bindings(p: Pattern) -> List(String) {
  case p {
    PAny -> []
    PTyp(_) -> []
    PLit(_) -> []
    PLitT(_) -> []
    PAlias(name, p) -> [name, ..bindings(p)]
    PCtr(_, p) -> bindings(p)
    PRcd(fields, opt_tail) -> {
      let xs = list.flat_map(fields, fn(kv) { bindings(kv.1) })
      let ys = case opt_tail {
        Some(tail) -> bindings(tail)
        None -> []
      }
      list.append(xs, ys)
    }
    PErr -> []
  }
}

pub fn lift(term: Term, names: List(String)) -> ast.Expr {
  let s = span.empty("", 0, 0)
  case term {
    Typ(u) -> ast.typ(u, s)
    Hole(id) if id < 0 -> ast.hole(None, s)
    Hole(id) -> ast.hole(Some(id), s)
    Lit(lit) -> ast.Expr(ast.Lit(lit), s)
    LitT(lit_t) -> ast.Expr(ast.LitT(lit_t), s)
    Var(index) ->
      case list_at(names, index) {
        Some(name) -> ast.var(name, s)
        None -> ast.var("`undefined " <> int.to_string(index) <> "`", s)
      }
    Ctr(tag, arg) -> ast.Expr(ast.Ctr(tag, lift(arg, names)), s)
    Rcd(fields, tail) -> {
      let fields_ast =
        list.map(fields, fn(field) {
          let #(name, #(term, default)) = field
          let term_ast = lift(term, names)
          let default_ast = option.map(default, lift(_, names))
          #(name, #(Some(term_ast), default_ast))
        })
      let tail_ast = option.map(tail, lift(_, names))
      ast.rcd(fields_ast, tail_ast, s)
    }
    Call(name, returns, args) -> todo
    Ann(term, type_) -> todo
    Lam(implicit, #(name, type_), body) -> {
      let type_ast = lift(type_, names)
      let body_ast = lift(body, [name, ..names])
      ast.lam(implicit, #(name, Some(type_ast)), body_ast, s)
    }
    Pi(implicit, #(name, type_), body) -> {
      let type_ast = lift(type_, names)
      let body_ast = lift(body, [name, ..names])
      ast.pi(implicit, #(name, Some(type_ast)), body_ast, s)
    }
    Fix(name, body) -> todo
    App(implicit, fun, arg) -> {
      let fun_ast = lift(fun, names)
      let arg_ast = lift(fun, names)
      ast.app(implicit, fun_ast, arg_ast, s)
    }
    TypeDef(type_def) -> todo
    Match(arg, cases) -> {
      let arg_ast = lift(arg, names)
      let cases_ast = list.map(cases, lift_case(_, names))
      ast.match(arg_ast, cases_ast, s)
    }
    Err -> ast.err(s)
  }
}

fn lift_case(c: Case, names: List(String)) -> ast.Case {
  let pattern_ast = lift_pattern(c.pattern)
  let names = list.append(bindings(c.pattern), names)
  let #(names, guard_ast) = case c.guard {
    Some(#(expr, pattern)) -> {
      let guard_ast = #(lift(expr, names), lift_pattern(pattern))
      let names = list.append(bindings(pattern), names)
      #(names, Some(guard_ast))
    }
    None -> #(names, None)
  }
  let body_ast = lift(c.body, names)
  ast.Case(pattern_ast, guard_ast, body_ast)
}

fn lift_pattern(p: Pattern) -> ast.Pattern {
  let s = span.empty("", 0, 0)
  case p {
    PAny -> ast.pany(s)
    PTyp(u) -> ast.ptyp(u, s)
    PLit(value) -> ast.plit(value, s)
    PLitT(lit_type) -> ast.plit_t(lit_type, s)
    PAlias(name, pattern) -> ast.palias(lift_pattern(pattern), name, s)
    PCtr(tag, pattern) -> ast.pctr(tag, lift_pattern(pattern), s)
    PRcd(fields, tail) -> {
      let fields_ast =
        list.map(fields, fn(field) {
          let #(name, pattern) = field
          #(name, lift_pattern(pattern))
        })
      let tail_ast = option.map(tail, lift_pattern)
      ast.prcd(fields_ast, tail_ast, s)
    }
    PErr -> todo
  }
}

// Syntax sugar

pub fn int(value: Int) -> Term {
  Lit(lit.Int(value))
}

pub fn float(value: Float) -> Term {
  Lit(lit.Float(value))
}

pub const int_t = LitT(lit.IntT)

pub const float_t = LitT(lit.FloatT)

pub const i8 = LitT(lit.I8)

pub const i16 = LitT(lit.I16)

pub const i32 = LitT(lit.I32)

pub const i64 = LitT(lit.I64)

pub const u8 = LitT(lit.U8)

pub const u16 = LitT(lit.U16)

pub const u32 = LitT(lit.U32)

pub const u64 = LitT(lit.U64)

pub const f32 = LitT(lit.F32)

pub const f64 = LitT(lit.F64)

pub fn rcd(fields: List(#(String, Term))) -> Term {
  rcd_open(fields, None)
}

pub fn rcd_open(fields: List(#(String, Term)), tail: Option(Term)) -> Term {
  let fields =
    list.map(fields, fn(field) {
      let #(name, value) = field
      #(name, #(value, None))
    })
  Rcd(fields, tail)
}

pub fn ctr(tag: String, args: List(#(String, Term))) -> Term {
  Ctr(tag, rcd(args))
}

pub fn lam(param: #(String, Type), body: Term) -> Term {
  Lam(False, param, body)
}

pub fn lam_implicit(param: #(String, Type), body: Term) -> Term {
  Lam(True, param, body)
}

pub fn app(fun: Term, arg: Term) -> Term {
  App(False, fun, arg)
}

pub fn app_implicit(fun: Term, arg: Term) -> Term {
  App(True, fun, arg)
}

pub fn let_var(def: #(String, Type, Term), body: Term) -> Term {
  let #(name, type_, value) = def
  app(lam(#(name, type_), body), value)
}

pub fn let_var_list(defs: List(#(String, Type, Term)), body: Term) -> Term {
  case defs {
    [] -> body
    [def, ..defs] -> let_var(def, let_var_list(defs, body))
  }
}

pub fn let_pat(def: #(Pattern, Term), body: Term) -> Term {
  let #(pattern, value) = def
  Match(value, [Case(pattern, None, body)])
}

pub fn dot(term: Term, field: String) -> Term {
  let pattern = PRcd([#(field, pvar(field))], Some(PAny))
  Match(term, [Case(pattern, None, Var(0))])
}

pub fn pvar(name: String) -> Pattern {
  PAlias(name, PAny)
}

pub fn pint(value: Int) -> Pattern {
  PLit(lit.Int(value))
}

pub fn pfloat(value: Float) -> Pattern {
  PLit(lit.Float(value))
}

pub fn prcd(fields: List(#(String, Pattern))) {
  prcd_tail(fields, PAny)
}

pub fn prcd_tail(fields: List(#(String, Pattern)), tail: Pattern) {
  PRcd(fields, Some(tail))
}

pub fn prcd_strict(fields: List(#(String, Pattern))) {
  PRcd(fields, None)
}
