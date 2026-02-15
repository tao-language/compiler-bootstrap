import core/ast.{
  type Term, Ann, App, Ctr, HVar, Lam, Pi, Span, Term, Typ, VCtr, VLam, VNeut,
  VPi, VTyp, Var,
}
import core/error.{Mismatch, NotAFunction, UnboundVariable}
import core/types
import gleam/option.{None}
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

pub fn infer_universe_test() {
  // Typetypype1
  case types.infer(0, [], typ(0)) {
    Ok(VTyp(1)) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn identity_type_check_test() {
  // (\x. x) : (A : Type0) -> A -> A
  // We check the lambda against the Pi type

  // Type: (A : Type0) -> (x : A) -> A
  // In DB: Pi "A" Type0 (Pi "x" (Var 0) (Var 1))
  // wait, Var 0 refers to A. Return type is A (Var 1 relative to inner?)
  // Actually simpler: id : (X: Type0) -> X
  // Pi "X" Type0 (Var 0)

  // Let's test simple identity: \x. x check against A -> A
  // We assume A is in context at index 0.

  let type_a = VTyp(0)
  // Mock value for type A
  let ctx = [#("A", type_a)]

  // Term: \x. x
  let term = lam("x", var(0))

  // Expected Type: A -> A
  // VPi "x" (Value A) (Closure returning Value A)
  let expected = VPi("x", VNeut(HVar(0), []), fn(_) { VNeut(HVar(0), []) })

  let result = types.check(1, ctx, term, expected)
  result |> should.be_ok
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
  // Context: A: Type, B: Type, f: A->A, b: B

  let ctx = [
    #("b", VTyp(0)),
    #("f", VPi("_", VTyp(1), fn(_) { VTyp(1) })),
  ]
  let b = var(0)
  let f = var(1)

  let term = app(f, b)
  types.infer(4, ctx, term)
  |> should.equal(Error(Mismatch(VTyp(1), VTyp(0), s(), None)))
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
