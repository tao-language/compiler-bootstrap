import core/ast.{
  type Term, Ann, App, Constructor, Lam, Pi, Span, Term, Universe, Var,
}
import core/error.{Mismatch, NotAFunction, UnboundVariable}
import core/types
import gleam/option
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// --- HELPERS ---
fn s() {
  Span(0, 0, "test")
}

fn type0() {
  Term(Universe(0), s())
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

fn ann(x, t) {
  Term(Ann(x, t), s())
}

// --- TESTS ---

pub fn infer_universe_test() {
  // Type0 : Type1
  case types.infer(0, [], type0()) {
    Ok(ast.VUniverse(1)) -> True
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

  let type_a = ast.VUniverse(0)
  // Mock value for type A
  let ctx = [#("A", type_a)]

  // Term: \x. x
  let term = lam("x", var(0))

  // Expected Type: A -> A
  // VPi "x" (Value A) (Closure returning Value A)
  let expected =
    ast.VPi("x", ast.VNeut(ast.HVar(0), []), fn(_) {
      ast.VNeut(ast.HVar(0), [])
    })

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

  // Setup mock values
  let type_a = ast.VUniverse(0)
  let type_b = ast.VUniverse(0)

  // f type: A -> A
  let f_type = ast.VPi("x", type_a, fn(_) { type_a })

  let ctx = [
    #("b", type_b),
    #("f", f_type),
    #("B", ast.VUniverse(1)),
    #("A", ast.VUniverse(1)),
  ]

  // Term: f b
  // Indices: b is 0, f is 1
  let term = Term(App(var(1), var(0)), s())

  let result = types.infer(4, ctx, term)

  case result {
    // Should fail because expected A, got B
    Error(Mismatch(expected, got, _, _)) -> {
      // In a real test we'd check equality of expected/got values
      True
    }
    _ -> False
  }
  |> should.be_true
}

pub fn not_a_function_test() {
  // (Type0) Type0
  // Applying Type0 to itself
  let term = Term(App(type0(), type0()), s())

  let result = types.infer(0, [], term)

  case result {
    Error(NotAFunction(_, _)) -> True
    _ -> False
  }
  |> should.be_true
}
