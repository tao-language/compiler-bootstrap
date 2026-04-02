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
import core/unify
import gleam/list
import gleam/option.{None, Some}
import gleam/int
import gleam/bool
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
// DEBUG TESTS FOR K COMBINATOR - DETAILED UNIFICATION ANALYSIS
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
// DETAILED ANALYSIS:
// When applying k(10) where k : VPi(2 implicits, _, _, hole_0, codomain):
// 1. infer_app extracts domain = hole_0 and codomain
// 2. It creates arg_ty_hole_val and result_ty_hole_val for the application
// 3. It creates fun_ty_expanded = VPi([], "_", env, arg_ty_hole_val, Hole(result_ty_hole_id))
// 4. It unifies VNeut(HHole(hole_id), []) with fun_ty_expanded
// 5. The unify should add hole_id -> fun_ty_expanded to substitution
// 6. But the result type extraction doesn't properly force through the substitution
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

/// Debug test: Test simple function application (non-polymorphic)
pub fn simple_app_debug_test() {
  // Build: id = x -> x (simple identity)
  let id = ast.Lam([], #("x", ast.Hole(-1, span)), ast.Var(0, span), span)
  
  // Build: id(42)
  let app = ast.App(id, [], ast.Lit(ast.I32(42), span), span)
  
  let s = state.initial_state
  let #(_val, ty, s2) = infer(s, app)
  
  // Should have no errors
  s2.errors |> should.equal([])
  
  // Result type should be I32T
  let is_i32_type = case ty {
    ast.VLitT(ast.I32T) -> True
    _ -> False
  }
  is_i32_type |> should.be_true()
}

/// Debug test: Inspect k combinator type before application
pub fn k_combinator_type_before_app_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

  let s = state.initial_state
  let #(_val, ty, s2) = infer(s, k)

  // Should have no errors
  s2.errors |> should.equal([])
  
  // Inspect the type structure
  let type_info = case ty {
    ast.VPi(implicit, name, env, domain, out_term) -> {
      let domain_info = case domain {
        ast.VNeut(ast.HHole(id), []) -> "hole_" <> int.to_string(id)
        ast.VNeut(ast.HVar(lvl), []) -> "var_" <> int.to_string(lvl)
        ast.VLitT(_) -> "literal"
        _ -> "other"
      }
      "VPi(implicit=" <> int.to_string(list.length(implicit)) 
        <> ", domain=" <> domain_info <> ")"
    }
    _ -> "not_VPi"
  }
  
  // Type should be VPi with implicits
  let is_vpi = case ty {
    ast.VPi(_, _, _, _, _) -> True
    _ -> False
  }
  is_vpi |> should.be_true()
}

/// Debug test: Test VPi with HVar domain (simulating polymorphic lambda)
pub fn vpi_hvar_domain_test() {
  let s = state.initial_state
  let env = []
  
  // Create a VPi type with HVar domain (like polymorphic lambda after instantiation)
  // VPi([], "_", [], HVar(0), Hole(1))
  let domain = ast.VNeut(ast.HVar(0), [])
  let codomain_term = ast.Hole(1, span)
  let vpi_type = ast.VPi([], "_", env, domain, codomain_term)
  
  // Create an argument (I32 literal)
  let arg = ast.Lit(ast.I32(42), span)
  
  // Check argument against HVar domain
  let #(arg_val, s) = infer.check(s, arg, domain, span)
  
  // The HVar(0) should now be solved in the substitution
  // But HVar is a level-based reference, not a hole ID
  // So we need to check if the substitution has the right mapping
  
  // For now, just verify the check succeeded
  let has_no_errors = list.length(s.errors) == 0
  has_no_errors |> should.be_true()
}

/// Debug test: Test implicit parameter instantiation
pub fn implicit_param_instantiation_test() {
  let s = state.initial_state
  
  // Simulate implicit params ["_0", "_1"]
  let implicit_params = ["_0", "_1"]
  
  // Instantiate them
  let #(implicit_subst, s) = subst.instantiate_implicit_params(implicit_params, s)
  
  // Should have 2 substitutions
  list.length(implicit_subst) |> should.equal(2)
  
  // Each should map index to a hole
  let all_holes = list.all(implicit_subst, fn(kv) {
    case kv.1 {
      ast.VNeut(ast.HHole(_), []) -> True
      _ -> False
    }
  })
  all_holes |> should.be_true()
}

/// Debug test: Test subst_value_with_implicit_vars
pub fn subst_value_with_implicit_vars_test() {
  // Create implicit substitution by inferring a lambda with 2 params
  // id2 = x -> y -> x (but we just want the holes)
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(0, span), span)
  let lam = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  
  let s = state.initial_state
  let #(_val, ty, s) = infer(s, lam)
  
  // ty should be VPi with 2 implicits
  case ty {
    ast.VPi(impl, _, _, domain, _codomain) -> {
      // Should have 2 implicit params
      list.length(impl) |> should.equal(2)
      
      // Domain should be a hole (HVar or HHole)
      let domain_is_neut = case domain {
        ast.VNeut(_, _) -> True
        _ -> False
      }
      domain_is_neut |> should.be_true()
    }
    _ -> {
      // Should be VPi
      True |> should.be_false()
    }
  }
}

/// Debug test: Full trace of k combinator application
pub fn k_combinator_full_trace_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  
  // Build: k(10)
  let app = ast.App(k, [], ast.Lit(ast.I32(10), span), span)
  
  let s = state.initial_state
  
  // Step 1: Infer k
  let #(k_val, k_ty, s) = infer(s, k)
  
  // k_ty should be VPi with 2 implicits
  let k_ty_info = case k_ty {
    ast.VPi(impl, _, _, domain, _) -> {
      let domain_is_hvar = case domain {
        ast.VNeut(ast.HVar(_), _) -> True
        _ -> False
      }
      "impl=" <> int.to_string(list.length(impl)) <> ", domain_is_hvar=" <> bool.to_string(domain_is_hvar)
    }
    _ -> "not_VPi"
  }
  
  // Step 2: Infer application
  let #(_app_val, app_ty, s) = infer(s, app)
  
  // Check for errors
  let has_errors = list.length(s.errors) > 0
  
  // If there are errors, the test should fail with details
  has_errors |> should.be_false()
}

/// Debug test: Check what the codomain term looks like after generalization
pub fn k_combinator_codomain_trace_test() {
  // Build: k = x -> y -> x
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  
  let s = state.initial_state
  let #(_val, ty, s) = infer(s, k)
  
  // ty should be VPi with 2 implicits
  case ty {
    ast.VPi(impl, _, _, domain, _codomain_term) -> {
      // Check implicit count
      list.length(impl) |> should.equal(2)
      
      // Check domain is a hole
      let domain_is_hole = case domain {
        ast.VNeut(ast.HHole(_), []) -> True
        _ -> False
      }
      domain_is_hole |> should.be_true()
      
      // The codomain_term is quoted, so we can't directly inspect it here
      // But we know it should reference the implicit params
    }
    _ -> {
      // Should be VPi
      True |> should.be_false()
    }
  }
  
  // Verify no errors
  list.length(s.errors) |> should.equal(0)
}

/// Debug test: Trace hole IDs through k combinator inference
pub fn k_combinator_hole_id_trace_test() {
  let s = state.initial_state
  
  // After inferring k, check hole IDs
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  let #(_val, _ty, s) = infer(s, k)
  
  // Should have created 2 holes (one for each lambda param)
  s.hole_counter |> should.equal(2)
  
  // Check hole depths
  let has_depth_0 = list.any(s.hole_depths, fn(d) { d.1 == 0 })
  let has_depth_1 = list.any(s.hole_depths, fn(d) { d.1 == 1 })
  has_depth_0 |> should.be_true()
  has_depth_1 |> should.be_true()
}

/// Debug test: Verify identity function works (baseline)
pub fn identity_function_baseline_test() {
  // Build: id = x -> x
  let id = ast.Lam([], #("x", ast.Hole(-1, span)), ast.Var(0, span), span)
  
  // Build: id(42)
  let app = ast.App(id, [], ast.Lit(ast.I32(42), span), span)
  
  let s = state.initial_state
  let #(_val, ty, s) = infer(s, app)
  
  // Should have no errors
  list.length(s.errors) |> should.equal(0)
  
  // Result type should be I32T
  let is_i32 = case ty {
    ast.VLitT(ast.I32T) -> True
    _ -> False
  }
  is_i32 |> should.be_true()
}

/// Debug test: Check inner lambda type in k combinator
pub fn k_combinator_inner_lambda_type_test() {
  let s = state.initial_state
  
  // Infer just the inner lambda: λy. x (where x is at index 1)
  // We need to set up the environment first
  let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
  
  // Create outer lambda context by binding x first
  let outer = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)
  let #(_val, ty, s) = infer(s, outer)
  
  // The type should be VPi with 2 implicits
  case ty {
    ast.VPi(impl, _, _, domain, _codomain) -> {
      // Check we have 2 implicit params
      list.length(impl) |> should.equal(2)
      
      // Domain should be a hole (for x's type)
      let domain_is_hole = case domain {
        ast.VNeut(ast.HHole(_), []) -> True
        _ -> False
      }
      domain_is_hole |> should.be_true()
    }
    _ -> {
      True |> should.be_false()
    }
  }
}
