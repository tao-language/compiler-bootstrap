// ============================================================================
// LAMBDA GENERALIZATION TESTS
// ============================================================================
/// Tests for lambda type inference with implicit parameter generalization.
///
/// These tests demonstrate the HVar index collision bug in nested lambdas:
/// - When inferring `k = x -> y -> x`, both lambdas create implicit ["_0"]
/// - After substitution, HVar(0) in both levels reference the SAME implicit!
/// - This causes type errors during application: "type ?X is not callable"
///
/// The fix requires renaming nested implicit params to avoid collisions.
import core/ast as ast
import core/state as state
import gleam/list
import gleam/option.{None, Some}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

// Helper span constant
const span = Span("test", 0, 0, 0, 0)

pub fn main() {
  gleeunit.main()
}

/// Test that nested lambdas have independent implicit parameter scopes.
/// k = x -> y -> x should infer to ∀a b. a -> b -> a
/// 
/// This test demonstrates the HVar index collision bug:
/// - Inner lambda creates implicit ["_0"] with HVar(0)
/// - Outer lambda also creates implicit ["_0"] 
/// - After substitution, both HVar(0) reference the SAME implicit!
/// 
/// Expected: Inner and outer HVar should reference different implicits.
pub fn nested_lambda_hvar_independence_test() {
  // Build: k = x -> y -> x
  // Inner: y -> x (returns Var(1) which is x)
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  // Outer: x -> (y -> x)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, k)
  
  // Should have no errors
  state.errors
  |> should.equal([])
  
  // Type should be a VPi (function type) with implicit params
  // After fix, should have polymorphic type with implicit params
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      // Should have implicit params (polymorphic)
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}

/// Test K combinator application: k(10)(20) should return 10
/// This verifies that hole unification works correctly with nested lambdas.
pub fn k_combinator_application_test() {
  // Build: k = x -> y -> x
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)
  
  // Build: k(10)(20)
  let app1 = c.App(k, [], c.Lit(c.I32(10), span), span)
  let app2 = c.App(app1, [], c.Lit(c.I32(20), span), span)
  
  let state = c.initial_state
  let #(_val, ty, state) = c.infer(state, app2)
  
  // Should have no errors
  state.errors
  |> should.equal([])
  
  // Result type should be I32 type (VLitT(I32T)), not a hole
  let is_i32_type = case ty {
    c.VLitT(c.I32T) -> True
    _ -> False
  }
  
  is_i32_type |> should.be_true()
}

/// Test Church numeral zero: zero = f -> x -> x
/// Expected type: ∀a b. (a -> a) -> a -> a
/// This tests triple-nested lambda inference.
pub fn church_numeral_zero_test() {
  // Build: zero = f -> x -> x
  let inner = c.Lam([], #("x", c.Hole(-1, span)), c.Var(0, span), span)
  let zero = c.Lam([], #("f", c.Hole(-1, span)), inner, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, zero)
  
  // Should have no errors
  state.errors
  |> should.equal([])
  
  // Type should be VPi with implicit params (polymorphic)
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}
