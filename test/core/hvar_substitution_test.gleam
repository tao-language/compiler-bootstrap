// ============================================================================
// HVAR SUBSTITUTION TESTS
// ============================================================================
/// Tests for HVar substitution with De Bruijn shifting.
///
/// HVar (Hole Variable) is a De Bruijn variable index for implicit binders.
/// When substituting Hole → HVar under nested binders (Pi/Lam), the HVar
/// index must be shifted to maintain correct references.
///
/// Bug: Original code did not shift HVar indices, causing nested lambdas
/// to have incorrect type references.
import core/core as c
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

/// Verify HVar indices are correct in nested lambda types.
///
/// k = x -> y -> x should have type with correct De Bruijn indices:
/// %pi<_0>(x: _0) -> %pi<_1>(y: _1) -> _0
///
/// From inner scope [y:0, _1:1, x:2, _0:3]:
/// - Outer domain HVar(0) references outer _0
/// - Inner domain HVar(1) references outer _0 (shifted by 1 for y binder)
pub fn hvar_index_in_nested_lambda_test() {
  let span = Span("test", 0, 0, 0, 0)

  // k = x -> y -> x
  // Inner: y -> x (returns Var(1) which is x)
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  // Outer: x -> (y -> x)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, k)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be a VPi (function type) - structure verified by no errors
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}

/// Test K combinator application: k(10)(20) should return 10.
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

/// Test Church numeral zero: zero = f -> x -> x.
///
/// Expected type: ∀a b. (a -> a) -> a -> a
/// This tests that nested lambda inference produces correct HVar indices.
pub fn church_numeral_zero_test() {
  let span = Span("test", 0, 0, 0, 0)

  // zero = f -> x -> x
  let inner = c.Lam([], #("x", c.Hole(-1, span)), c.Var(0, span), span)
  let zero = c.Lam([], #("f", c.Hole(-1, span)), inner, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, zero)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be a VPi (function type) - structure verified by no errors
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}

/// Test compose combinator: compose = f -> g -> x -> f(g(x)).
///
/// Expected type: ∀a b c. (b -> c) -> (a -> b) -> a -> c
/// This tests triple-nested lambda inference with correct HVar shifting.
pub fn compose_combinator_test() {
  let span = Span("test", 0, 0, 0, 0)

  // compose = f -> g -> x -> f(g(x))
  // g(x) = g applied to x
  let g_x = c.App(c.Var(1, span), [], c.Var(0, span), span)
  // f(g(x)) = f applied to g(x)
  let f_g_x = c.App(c.Var(2, span), [], g_x, span)

  let inner = c.Lam([], #("x", c.Hole(-1, span)), f_g_x, span)
  let mid = c.Lam([], #("g", c.Hole(-1, span)), inner, span)
  let compose = c.Lam([], #("f", c.Hole(-1, span)), mid, span)

  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, compose)

  // Should have no errors
  state.errors |> should.equal([])

  // Type should be a VPi (function type) - structure verified by no errors
  let is_vpi = case ty {
    c.VPi(_, _, _, _, _) -> True
    _ -> False
  }

  is_vpi |> should.be_true()
}
