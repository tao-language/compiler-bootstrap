import core/ast.{
  type Case, type Pattern, type Span, type Term, type Value, Ann, App, Ctr, HVar,
  Hole, Lam, Match, PAny, PCtr, PVar, Pi, Span, Term, Typ, VCtr, VLam, VNeut,
  VPi, VTyp, Var,
}
import core/error.{Mismatch as TypeMismatch, NotAFunction, UnboundVariable}
import core/types
import gleam/option.{None, Some}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// --- HELPERS ---
fn s() {
  Span(0, 0, "test")
}

fn typ(i) {
  Term(Typ(i), s())
}

fn var(i) {
  Term(Var(i), s())
}

fn pi(n, d, c) {
  Term(Pi(n, d, c), s())
}

fn lam(n, b) {
  Term(Lam(n, b), s())
}

fn app(f, a) {
  Term(App(f, a), s())
}

fn ann(x, t) {
  Term(Ann(x, t), s())
}

// --- TESTS ---
pub fn ctx_get_test() {
  let a = #("x", VTyp(1))
  let b = #("y", VTyp(2))
  types.ctx_get([], 0) |> should.be_none
  types.ctx_get([a], 0) |> should.equal(Some(a))
  types.ctx_get([a, b], 0) |> should.equal(Some(a))
  types.ctx_get([a, b], 1) |> should.equal(Some(b))
}

pub fn typ_infer_test() {
  types.infer(42, [], typ(0)) |> should.equal(Ok(VTyp(1)))
}

pub fn typ_check_test() {
  types.check(42, [], typ(0), VTyp(1)) |> should.be_ok
  types.check(42, [], typ(0), VTyp(2))
  |> should.equal(Error(TypeMismatch(VTyp(2), VTyp(1), s(), None)))
}

pub fn var_infer_test() {
  let ctx = [#("x", VTyp(0))]
  types.infer(42, ctx, var(0)) |> should.equal(Ok(VTyp(0)))
  types.infer(42, ctx, var(1))
  |> should.equal(Error(UnboundVariable(1, s())))
}

pub fn identity_type_check_test() {
  // Term: \x. x
  // Type: A -> A
  let ctx = [#("A", VTyp(0))]
  let term = lam("x", var(0))
  let term_ty = VPi("x", VNeut(HVar(0), []), fn(_) { VNeut(HVar(0), []) })
  types.check(1, ctx, term, term_ty)
  |> should.be_ok
}

pub fn unbound_variable_error_test() {
  // x (where x is not in context)
  let term = var(0)
  let result = types.infer(0, [], term)

  case result {
    Error(UnboundVariable(0, _)) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn application_mismatch_test() {
  // (f : A -> A) applied to (b : B)
  let a_ty = VTyp(0)
  let b_ty = VTyp(1)
  let ctx = [
    #("b", b_ty),
    #("f", VPi("_", a_ty, fn(_) { a_ty })),
  ]
  let b = var(0)
  let f = var(1)

  let term = app(f, b)
  types.infer(4, ctx, term)
  |> should.equal(Error(TypeMismatch(a_ty, b_ty, s(), None)))
}

pub fn not_a_function_test() {
  // (Type0) Type0
  // Applying Type0 to itself
  let term = Term(App(typ(0), typ(0)), s())

  let result = types.infer(0, [], term)

  case result {
    Error(NotAFunction(_, _)) -> True
    _ -> False
  }
  |> should.be_true
}
