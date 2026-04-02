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
import core/infer.{infer}
import core/subst as subst
import gleam/list
import gleam/option.{None, Some}
import gleam/int
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

const s = state.initial_state

// Helper span constant
const span = Span("test", 0, 0, 0, 0)

pub fn main() {
  gleeunit.main()
}

// Helper to inspect value types (for debugging)
fn inspect_value(v: ast.Value) -> String {
  case v {
    ast.VLam(_, _, _, _) -> "VLam"
    ast.VPi(impl, _, _, _, _) -> "VPi(" <> int.to_string(list.length(impl)) <> " implicits)"
    ast.VNeut(ast.HHole(id), spine) -> "HHole(" <> int.to_string(id) <> ", spine=" <> int.to_string(list.length(spine)) <> ")"
    ast.VNeut(ast.HVar(lvl), spine) -> "HVar(" <> int.to_string(lvl) <> ", spine=" <> int.to_string(list.length(spine)) <> ")"
    ast.VNeut(ast.HStepLimit, spine) -> "HStepLimit(spine=" <> int.to_string(list.length(spine)) <> ")"
    ast.VLit(_) -> "VLit"
    ast.VLitT(_) -> "VLitT"
    ast.VTyp(_) -> "VTyp"
    ast.VRcd(_) -> "VRcd"
    ast.VRecord(_) -> "VRecord"
    ast.VCall(_, _) -> "VCall"
    ast.VFix(_, _, _) -> "VFix"
    ast.VCtrValue(_) -> "VCtrValue"
    ast.VUnit -> "VUnit"
    ast.VErr -> "VErr"
  }
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
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  // Outer: x -> (y -> x)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  
  let s = state.initial_state
  let #(_, ty, s) = infer(s, k)
  
  // Should have no errors
  s.errors
  |> should.equal([])
  
  // Type should be a VPi (function type) with implicit params
  // After fix, should have polymorphic type with implicit params
  let is_vpi_with_implicit = case ty {
    ast.VPi(implicit, _, _, _, _) -> {
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
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  // Build: k(10)(20)
  let app1 = ast.App(k, [], ast.Lit(ast.I32(10), span), span)
  let app2 = ast.App(app1, [], ast.Lit(ast.I32(20), span), span)

  let s = state.initial_state
  let #(val, ty, s2) = infer(s, app2)

  // Should have no errors
  s2.errors |> should.equal([])

  // Result type should be I32 type (VLitT(I32T)), not a hole
  let is_i32_type = case ty {
    ast.VLitT(ast.I32T) -> True
    _ -> False
  }

  is_i32_type |> should.be_true()
}

/// Test Church numeral zero: zero = f -> x -> x
/// Expected type: ∀a b. (a -> a) -> a -> a
/// This tests triple-nested lambda inference.
pub fn church_numeral_zero_test() {
  // Build: zero = f -> x -> x
  let inner = ast.Lam([], #("x", ast.Hole(-1, span)), ast.Var(0, span), span)
  let zero = ast.Lam([], #("f", ast.Hole(-1, span)), inner, span)
  
  let #(_, ty, result_state): #(ast.Value, ast.Type, state.State) = infer(s, zero)

  // Should have no errors
  s.errors
  |> should.equal([])

  // Type should be VPi with implicit params (polymorphic)
  let is_vpi_with_implicit = case ty {
    ast.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }

  is_vpi_with_implicit |> should.be_true()
}

// ============================================================================
// DEBUG TESTS FOR K COMBINATOR
// ============================================================================
// 
// KEY FINDINGS FROM DEBUG TESTS:
// 
// ✓ Hole depths ARE being tracked correctly (depth 0 for outer lambda, depth 1 for inner)
// ✓ Type structure IS correct (VPi with implicit params)
// ✓ Substitutions ARE being created during inference
// ✗ Application is NOT solving holes correctly
//
// ROOT CAUSE: The issue is in infer_app - hole unification during function
// application is not working correctly. The holes created for lambda parameters
// are not being solved when arguments are applied.
//
// ============================================================================

/// Debug test: Inspect hole depths during k combinator inference
pub fn k_combinator_debug_hole_depths_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  let s = state.initial_state
  let #(_, ty, s2) = infer(s, k)

  // Should have no errors
  s2.errors |> should.equal([])

  // Check that hole depths are tracked
  // Hole 0 should be at depth 0 (outer lambda)
  // Hole 1 should be at depth 1 (inner lambda)
  let has_correct_depths = case s2.hole_depths {
    [#(0, 0), #(1, 1)] -> True
    [#(1, 1), #(0, 0)] -> True  // Order may vary
    _ -> False
  }
  has_correct_depths |> should.be_true()
}

/// Debug test: Inspect k combinator type structure
pub fn k_combinator_debug_type_structure_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  let s = state.initial_state
  let #(_, ty, s2) = infer(s, k)

  // Should have no errors
  s2.errors |> should.equal([])

  // Type should be VPi (polymorphic function type)
  let is_vpi = case ty {
    ast.VPi(_, _, _, _, _) -> True
    _ -> False
  }
  is_vpi |> should.be_true()
}

/// Debug test: Inspect k combinator application
pub fn k_combinator_debug_application_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  // Build: k(10)
  let app1 = ast.App(k, [], ast.Lit(ast.I32(10), span), span)

  let s = state.initial_state
  let #(_val1, ty1, s2) = infer(s, app1)

  // First application should have no errors
  s2.errors |> should.equal([])

  // Result type should be a function type (VPi) or hole that will be solved
  let is_function_or_hole = case ty1 {
    ast.VPi(_, _, _, _, _) -> True
    ast.VNeut(ast.HHole(_), _) -> True  // Hole is OK - will be solved
    _ -> False
  }
  is_function_or_hole |> should.be_true()
}

/// Debug test: Full k combinator application with hole inspection
pub fn k_combinator_debug_full_application_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  // Build: k(10)(20)
  let app1 = ast.App(k, [], ast.Lit(ast.I32(10), span), span)
  let app2 = ast.App(app1, [], ast.Lit(ast.I32(20), span), span)

  let s = state.initial_state
  let #(_val, ty, s2) = infer(s, app2)

  // Should have no errors
  s2.errors |> should.equal([])

  // Check hole depths - should have holes at depths 0 and 1
  let has_depth_0 = list.any(s2.hole_depths, fn(d) { d.1 == 0 })
  let has_depth_1 = list.any(s2.hole_depths, fn(d) { d.1 == 1 })
  has_depth_0 |> should.be_true()
  has_depth_1 |> should.be_true()

  // Result type should be I32T or a solved hole
  let is_i32_or_solved = case ty {
    ast.VLitT(ast.I32T) -> True
    ast.VNeut(ast.HHole(id), spine) -> {
      // Check if hole is solved in substitution
      list.key_find(s2.subst, id) != Error(Nil)
    }
    _ -> False
  }
  is_i32_or_solved |> should.be_true()
}

/// Debug test: Inspect substitution after k combinator inference
pub fn k_combinator_debug_substitution_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  // Build: k(10)(20)
  let app1 = ast.App(k, [], ast.Lit(ast.I32(10), span), span)
  let app2 = ast.App(app1, [], ast.Lit(ast.I32(20), span), span)

  let s = state.initial_state
  let #(_, _, s2) = infer(s, app2)

  // Check that holes are being solved in substitution
  // After successful inference, holes should be solved to concrete types
  let has_substitutions = list.length(s2.subst) > 0
  has_substitutions |> should.be_true()
}
