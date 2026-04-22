// ============================================================================
// CORE VISITOR TESTS
// ============================================================================
/// Tests for the generic AST visitor in core/visitor.gleam.
import core/ast as ast
import core/visitor as visitor
import syntax/grammar.{type Span, Span}
import gleeunit
import gleeunit/should
import gleam/option.{None}

const s0 = Span("visitor_test", 0, 0, 0, 0)
const s1 = Span("visitor_test", 1, 1, 1, 1)

fn eq_terms(a: ast.Term, b: ast.Term) -> Bool { a == b }
fn eq_patterns(a: ast.Pattern, b: ast.Pattern) -> Bool { a == b }

fn var_(i, s) { ast.Var(i, s) }
fn hole_(i, s) { ast.Hole(i, s) }
fn i32_(v, s) { ast.Lit(ast.I32(v), s) }

// Build callbacks tuple for visit_term
fn mk_callbacks() -> #(
  fn(Int, Span) -> ast.Term,
  fn(Int, Span) -> ast.Term,
  fn(List(String), #(String, ast.Term), ast.Term, Span) -> ast.Term,
  fn(List(String), String, ast.Term, ast.Term, Span) -> ast.Term,
  fn(ast.Term, List(ast.Term), ast.Term, Span) -> ast.Term,
  fn(ast.Term, ast.Term, List(ast.Case), Span) -> ast.Term,
  fn(String, ast.Term, Span) -> ast.Term,
  fn(List(#(String, ast.Term)), Span) -> ast.Term,
  fn(ast.Term, String, Span) -> ast.Term,
  fn(ast.Term, ast.Term, Span) -> ast.Term,
  fn(String, List(#(ast.Term, ast.Term)), ast.Term, Span) -> ast.Term,
  fn(ast.Term, Span) -> ast.Term,
  fn(String, ast.Term, Span) -> ast.Term,
  fn(String, ast.Term, ast.Term, Span) -> ast.Term,
  fn(Int, Span) -> ast.Term,
  fn(ast.Literal, Span) -> ast.Term,
  fn(ast.LiteralType, Span) -> ast.Term,
  fn(Span) -> ast.Term,
  fn(String, Span) -> ast.Term,
) {
  let v = fn(i, s) { var_(i, s) }
  let h = fn(i, s) { hole_(i, s) }
  let l = fn(imp, p, b, s) { ast.Lam(imp, p, b, span: s) }
  let p = fn(imp, n, it, ot, s) { ast.Pi(imp, n, in_term: it, out_term: ot, span: s) }
  let a = fn(f, imp, ar, s) { ast.App(f, implicit: imp, arg: ar, span: s) }
  let m = fn(agg, mot, cs, s) { ast.Match(agg, motive: mot, cases: cs, span: s) }
  let c = fn(t, ar, s) { ast.Ctr(t, arg: ar, span: s) }
  let r = fn(fs, s) { ast.Rcd(fs, span: s) }
  let d = fn(agg, f, s) { ast.Dot(agg, field: f, span: s) }
  let n = fn(tm, tp, s) { ast.Ann(term: tm, typ: tp, span: s) }
  let cl = fn(name, args, ret, s) { ast.Call(name, args: args, ret: ret, span: s) }
  let co = fn(t, s) { ast.Comptime(t, span: s) }
  let fx = fn(name, b, s) { ast.Fix(name, body: b, span: s) }
  let lt = fn(name, val, b, s) { ast.Let(name, value: val, body: b, span: s) }
  let ty = fn(l, s) { ast.Typ(l, span: s) }
  let li = fn(v, s) { ast.Lit(v, s) }
  let lt_ = fn(t, s) { ast.LitT(t, span: s) }
  let u = fn(s) { ast.Unit(s) }
  let e = fn(m, s) { ast.Err(m, span: s) }
  #(v, h, l, p, a, m, c, r, d, n, cl, co, fx, lt, ty, li, lt_, u, e)
}

fn true_eq(a: a, b: a) -> Bool { a == b }

// --- IDENTITY TESTS ---

pub fn visitor_identity_var_test() {
  let term = var_(0, s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_identity_lam_test() {
  let body = ast.Hole(0, s0)
  let term = ast.Lam([], #( "x", body ), body, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_identity_nested_lam_test() {
  let inner = ast.Lam([], #( "y", var_(0, s0) ), var_(0, s0), span: s0)
  let outer = ast.Lam([], #( "x", inner ), inner, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(outer, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, outer) |> should.equal(True)
}

// --- SIMPLE CONSTRUCTORS ---

pub fn visitor_identity_type_test() {
  let term = ast.Typ(0, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_identity_hole_test() {
  let term = ast.Hole(42, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_identity_unit_test() {
  let term = ast.Unit(s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

// --- HOLES-TO-VARS TRANSFORMATION ---

pub fn visitor_hole_to_var_test() {
  let term = ast.Hole(5, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(
    term, c.0,
    fn(id, s) { var_(id, s) },
    c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18,
  )
  true_eq(result, var_(5, s0)) |> should.equal(True)
}

pub fn visitor_hole_to_var_nested_test() {
  let term = ast.Lam([], #( "x", ast.Hole(3, s0) ), ast.Hole(3, s0), span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(
    term, c.0,
    fn(id, s) { var_(id, s) },
    c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18,
  )
  case result {
    ast.Lam(_, _, body, _) -> true_eq(body, var_(3, s0)) |> should.equal(True)
    _ -> panic("expected Lam")
  }
}

// --- COMPLEX TERM TRAVERSAL ---

pub fn visitor_match_test() {
  let arg = var_(0, s0)
  let motive = ast.Typ(0, s1)
  let case1 = ast.Case(ast.PAny, var_(0, s1), guard: None, span: s1)
  let cases = [case1]
  let term = ast.Match(arg, motive: motive, cases: cases, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_pi_test() {
  let in_t = ast.LitT(ast.I32T, s0)
  let out_t = ast.LitT(ast.I64T, s0)
  let term = ast.Pi([], "x", in_term: in_t, out_term: out_t, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_app_test() {
  let fun = ast.Lam([], #( "f", var_(0, s1) ), var_(0, s1), span: s0)
  let arg = ast.Lit(ast.I32(42), s1)
  let term = ast.App(fun, implicit: [], arg: arg, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_record_test() {
  let fields = [#("x", i32_(1, s0)), #("y", ast.Lit(ast.I64(2), s0))]
  let term = ast.Rcd(fields, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_dot_test() {
  let arg = var_(0, s0)
  let term = ast.Dot(arg, field: "x", span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_annotation_test() {
  let term = ast.Ann(term: var_(0, s0), typ: ast.LitT(ast.I32T, s1), span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_let_test() {
  let value = i32_(1, s0)
  let body = var_(0, s1)
  let term = ast.Let("x", value: value, body: body, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_fix_test() {
  let body = var_(0, s0)
  let term = ast.Fix("f", body: body, span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_comptime_test() {
  let term = ast.Comptime(i32_(42, s0), span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_call_test() {
  let term = ast.Call("eq", args: [#(var_(0, s0), ast.LitT(ast.I32T, s1))], ret: ast.LitT(ast.ILitT, s0), span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

pub fn visitor_error_term_test() {
  let term = ast.Err("Something went wrong", span: s0)
  let c = mk_callbacks()
  let result = visitor.visit_term(term, c.0, c.1, c.2, c.3, c.4, c.5, c.6, c.7, c.8, c.9, c.10, c.11, c.12, c.13, c.14, c.15, c.16, c.17, c.18)
  true_eq(result, term) |> should.equal(True)
}

// --- PATTERN VISITOR TESTS ---

pub fn visitor_pattern_ctr_test() {
  let pattern = ast.PCtr("Some", ast.PAny)
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PCtr("Some", ast.PAny)) |> should.equal(True)
}

pub fn visitor_pattern_rcd_test() {
  let pattern = ast.PRcd([#("x", ast.PAny), #("y", ast.PAny)])
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, pattern) |> should.equal(True)
}

pub fn visitor_pattern_as_test() {
  let pattern = ast.PAs(ast.PAny, "x")
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PAs(ast.PAny, "x")) |> should.equal(True)
}

pub fn visitor_pattern_nested_as_ctr_test() {
  let pattern = ast.PAs(ast.PCtr("Some", ast.PAny), "wrapped")
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PAs(ast.PCtr("Some", ast.PAny), "wrapped")) |> should.equal(True)
}

pub fn visitor_pattern_unit_test() {
  let pattern = ast.PUnit
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PUnit) |> should.equal(True)
}

pub fn visitor_pattern_any_test() {
  let pattern = ast.PAny
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PAny) |> should.equal(True)
}

pub fn visitor_pattern_lit_t_test() {
  let pattern = ast.PLitT(ast.I32T)
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PLitT(ast.I32T)) |> should.equal(True)
}

pub fn visitor_pattern_typ_test() {
  let pattern = ast.PTyp(0)
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PTyp(0)) |> should.equal(True)
}

pub fn visitor_pattern_lit_test() {
  let pattern = ast.PLit(ast.I32(42))
  let result = visitor.visit_pattern(
    pattern,
    fn(tag, arg) { ast.PCtr(tag, arg) },
    fn(fields) { ast.PRcd(fields) },
  )
  eq_patterns(result, ast.PLit(ast.I32(42))) |> should.equal(True)
}

pub fn main() {
  gleeunit.main()
}
