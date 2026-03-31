// ============================================================================
// HVAR FIX TESTS
// ============================================================================
/// Tests for the lambda generalization fix with De Bruijn shifting.
///
/// This tests the fix for nested polymorphic lambda type inference.
/// The bug was that HVar indices were not shifted when entering nested binders
/// during implicit parameter instantiation, causing incorrect substitution.
import core/core as c
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

/// Test 1: Verify k = x -> y -> x infers without errors.
///
/// After the fix, nested lambda type inference should work correctly.
pub fn k_combinator_type_structure_test() {
  let span = Span("test", 0, 0, 0, 0)

  // k = x -> y -> x
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, k)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be a VPi (function type)
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}

/// Test 2: Test K combinator application: k(10)(20) should work.
///
/// This verifies that hole unification works correctly with nested lambdas.
pub fn k_combinator_application_test() {
  let span = Span("test", 0, 0, 0, 0)

  // k = x -> y -> x
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)

  // k(10)(20)
  let app1 = c.App(k, [], c.Lit(c.I32(10), span), span)
  let app2 = c.App(app1, [], c.Lit(c.I32(20), span), span)

  let state = c.initial_state
  let #(_val, ty, state) = c.infer(state, app2)

  // Should have no errors
  state.errors |> should.equal([])

  // Result type should be I32 (not a hole)
  let is_i32_type = case ty {
    c.VLitT(c.I32T) -> True
    _ -> False
  }

  is_i32_type |> should.be_true()
}

/// Test 3: Test Church numeral zero: zero = f -> x -> x.
///
/// Expected type: ∀a b. (a -> a) -> a -> a
pub fn church_numeral_zero_test() {
  let span = Span("test", 0, 0, 0, 0)

  // zero = f -> x -> x
  let inner = c.Lam([], #("x", c.Hole(-1, span)), c.Var(0, span), span)
  let zero = c.Lam([], #("f", c.Hole(-1, span)), inner, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, zero)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be VPi (function type)
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}

/// Test 4: Test compose combinator: compose = f -> g -> x -> f(g(x)).
///
/// Expected type: ∀a b c. (b -> c) -> (a -> b) -> a -> c
pub fn compose_combinator_test() {
  let span = Span("test", 0, 0, 0, 0)

  // compose = f -> g -> x -> f(g(x))
  let g_x = c.App(c.Var(1, span), [], c.Var(0, span), span)
  let f_g_x = c.App(c.Var(2, span), [], g_x, span)

  let inner = c.Lam([], #("x", c.Hole(-1, span)), f_g_x, span)
  let mid = c.Lam([], #("g", c.Hole(-1, span)), inner, span)
  let compose = c.Lam([], #("f", c.Hole(-1, span)), mid, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, compose)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be VPi (function type)
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}

/// Test 5: Test Church numeral successor application.
///
/// succ = n -> f -> x -> f(n f x)
/// succ(zero) should work without "type ?X is not callable" errors
pub fn church_numeral_succ_application_test() {
  let span = Span("test", 0, 0, 0, 0)

  // zero = f -> x -> x
  let zero_inner = c.Lam([], #("x", c.Hole(-1, span)), c.Var(0, span), span)
  let zero = c.Lam([], #("f", c.Hole(-1, span)), zero_inner, span)

  // succ = n -> f -> x -> f(n f x)
  let n_f = c.App(c.Var(2, span), [], c.Var(1, span), span)
  let n_f_x = c.App(n_f, [], c.Var(0, span), span)
  let f_n_f_x = c.App(c.Var(1, span), [], n_f_x, span)
  let succ_inner = c.Lam([], #("x", c.Hole(-1, span)), f_n_f_x, span)
  let succ_mid = c.Lam([], #("f", c.Hole(-1, span)), succ_inner, span)
  let succ = c.Lam([], #("n", c.Hole(-1, span)), succ_mid, span)

  // succ(zero)
  let app = c.App(succ, [], zero, span)

  let state = c.initial_state
  let #(_, _, state) = c.infer(state, app)

  // Should have no errors
  state.errors |> should.equal([])
}
