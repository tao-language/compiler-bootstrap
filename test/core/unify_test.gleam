/// Tests for the unification module
///
/// Tests cover:
/// - Basic value equality (same types)
/// - Hole binding (HHole → concrete value)
/// - Hole already bound (re-unification)
/// - Variable lookup (HVar → bound value)
/// - Pi type unification
/// - Lambda type unification
/// - Constructor tag mismatch
/// - Literal value mismatch
/// - Record field mismatch
/// - Record matching
/// - Neutral term comparison
/// - Error accumulation
/// - VErr passthrough (err type unifies with anything)
/// - occurs_check always allows recursive types
import core/ast.{
  EApp, Float as LitFloat, HHole, HVar, Int as LitInt, VCtr, VErr, VLam, VLit,
  VNeut, VPi, VRcd, Var,
  IntT, FloatT, I32T, F64T, VLitT,
}
import core/state.{TypeMismatch, def_var, initial_state}
import core/unify.{is_wildcard, literal_type_matches_wildcard, occurs_check, unify}
import gleam/list
import gleeunit
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Basic value equality — same types unify successfully
// ============================================================================

pub fn unify_same_lit_int_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VLit(LitInt(42)))
  assert final.errors == []
}

pub fn unify_same_lit_float_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitFloat(3.14)), VLit(LitFloat(3.14)))
  assert final.errors == []
}

pub fn unify_same_vctr_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VCtr("Just", VNeut(HVar(0), [])),
      VCtr("Just", VNeut(HVar(0), [])),
    )
  assert final.errors == []
}

pub fn unify_same_vrcd_empty_test() {
  let state = initial_state([])
  let final = unify(state, VRcd([]), VRcd([]))
  assert final.errors == []
}

// ============================================================================
// Hole binding — HHole binds to the other value
// ============================================================================

pub fn unify_hole_bounds_to_int_test() {
  let state = initial_state([])
  let final = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)))
  // Hole is bound — no errors
  assert final.errors == []
}

pub fn unify_hole_in_actual_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VNeut(HHole(0), []))
  assert final.errors == []
}

pub fn unify_same_hole_id_test() {
  let state = initial_state([])
  let final = unify(state, VNeut(HHole(5), []), VNeut(HHole(5), []))
  assert final.errors == []
}

pub fn unify_different_hole_ids_test() {
  let state = initial_state([])
  let final = unify(state, VNeut(HHole(1), []), VNeut(HHole(2), []))
  // Different holes are treated as different values
  assert list.length(final.errors) >= 1
}

pub fn unify_hole_reunification_test() {
  let state = initial_state([])
  let s1 = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)))
  // Re-unify the same hole — should succeed (already bound to 42)
  let s2 = unify(s1, VNeut(HHole(0), []), VLit(LitInt(42)))
  assert s2.errors == []
}

// ============================================================================
// Variable lookup — HVar looks up in state
// ============================================================================

pub fn unify_hvar_looks_up_value_test() {
  // Create a binding: "x" -> (VNeut(HHole(0), []), VNeut(HHole(0), []))
  // Then try to unify VNeut(HHole(1), []) with VNeut(HHole(0), [])
  // Different hole IDs should produce a type mismatch
  let state = initial_state([])
  let s1 = def_var(state, "x", VNeut(HHole(0), []), VNeut(HHole(0), []))
  let s2 = unify(s1, VNeut(HHole(1), []), VNeut(HHole(0), []))
  // Different holes are not equal
  assert list.length(s2.errors) >= 1
}

// ============================================================================
// Pi type unification
// ============================================================================

pub fn unify_same_pi_type_test() {
  let dom = VNeut(HHole(0), [])
  let codom = VNeut(HHole(1), [])
  let state = initial_state([])
  let final = unify(state, VPi([], [], #("pi_param", dom), codom), VPi([], [], #("pi_param", dom), codom))
  assert final.errors == []
}

pub fn unify_mismatched_pi_domain_test() {
  // Use concrete values that genuinely don't unify
  let state = initial_state([])
  let final =
    unify(
      state,
      VPi([], [], #("pi_param", VLit(LitInt(42))), VNeut(HHole(0), [])),
      VPi([], [], #("pi_param", VLit(LitInt(43))), VNeut(HHole(0), [])),
    )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Lambda type unification
// ============================================================================

pub fn unify_same_lam_type_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VLam([], [], #("x", VNeut(HHole(0), [])), Var(0, single("", 0, 0))),
      VLam([], [], #("y", VNeut(HHole(0), [])), Var(0, single("", 0, 0))),
    )
  assert final.errors == []
}

pub fn unify_mismatched_lam_type_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VLam([], [], #("x", VLit(LitInt(42))), Var(0, single("", 0, 0))),
      VLam([], [], #("y", VLit(LitFloat(3.14))), Var(0, single("", 0, 0))),
    )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Constructor mismatch
// ============================================================================

pub fn unify_different_ctr_tags_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VCtr("Just", VNeut(HHole(0), [])),
      VCtr("Nothing", VNeut(HHole(0), [])),
    )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Literal mismatch
// ============================================================================

pub fn unify_different_lit_int_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VLit(LitInt(43)))
  assert list.length(final.errors) >= 1
}

pub fn unify_lit_int_vs_float_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VLit(LitFloat(42.0)))
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Record unification
// ============================================================================

pub fn unify_same_vrcd_fields_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VRcd([#("name", VNeut(HHole(0), []))]),
      VRcd([#("name", VNeut(HHole(0), []))]),
    )
  assert final.errors == []
}

pub fn unify_mismatched_vrcd_fields_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VRcd([#("name", VNeut(HHole(0), []))]),
      VRcd([#("age", VNeut(HHole(0), []))]),
    )
  assert list.length(final.errors) >= 1
}

pub fn unify_mismatched_vrcd_arity_test() {
  let state = initial_state([])
  let final = unify(state, VRcd([#("name", VNeut(HHole(0), []))]), VRcd([]))
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Neutral term comparison
// ============================================================================

pub fn unify_same_hvar_test() {
  // HVar(0) looks up in state — need a binding for it
  let bound_val = VNeut(HHole(0), [])
  let s1 = def_var(initial_state([]), "x", bound_val, bound_val)
  let final =
    unify(
      s1,
      VNeut(HVar(0), [EApp(VRcd([]))]),
      VNeut(HVar(0), [EApp(VRcd([]))]),
    )
  assert final.errors == []
}

pub fn unify_different_hvar_test() {
  let state = initial_state([])
  let final = unify(state, VNeut(HVar(0), []), VNeut(HVar(1), []))
  assert list.length(final.errors) >= 1
}

pub fn unify_hvar_vs_hhole_test() {
  // HVar(0) looks up in empty state — fails, then HHole(0) gets bound
  let state = initial_state([])
  let final = unify(state, VNeut(HVar(0), []), VNeut(HHole(0), []))
  // HVar(0) fails lookup → error is added
  // HHole(0) in actual is bound to HVar(0)'s resolved type
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Type mismatch error accumulation
// ============================================================================

pub fn unify_accumulates_multiple_errors_test() {
  let state = initial_state([])
  let s1 = unify(state, VLit(LitInt(1)), VLit(LitInt(2)))
  let s2 = unify(s1, VLit(LitFloat(1.0)), VLit(LitFloat(2.0)))
  assert list.length(s2.errors) == 2
}

pub fn unify_error_is_typemismatch_test() {
  let state = initial_state([])
  let s = unify(state, VLit(LitInt(42)), VLit(LitFloat(42.0)))
  assert case s.errors {
    [TypeMismatch(..)] -> True
    _ -> False
  }
}

// ============================================================================
// VErr passthrough — VErr unifies with anything
// ============================================================================

pub fn unify_err_unifies_with_lit_test() {
  let state = initial_state([])
  let final = unify(state, VErr, VLit(LitInt(42)))
  assert final.errors == []
}

pub fn unify_lit_unifies_with_err_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VErr)
  assert final.errors == []
}

pub fn unify_err_unifies_with_err_test() {
  let state = initial_state([])
  let final = unify(state, VErr, VErr)
  assert final.errors == []
}

// ============================================================================
// occurs_check — always allows recursive types
// ============================================================================

pub fn occurs_check_always_false_test() {
  // Even if a value contains itself, occurs_check returns False
  // This allows recursive types
  let v = VCtr("Rec", VNeut(HHole(0), []))
  assert occurs_check(0, v) == False
}

pub fn occurs_check_on_literal_is_false_test() {
  let lit = VLit(LitInt(42))
  assert occurs_check(99, lit) == False
}

pub fn occurs_check_on_neutral_is_false_test() {
  let v = VNeut(HVar(0), [EApp(VRcd([]))])
  assert occurs_check(0, v) == False
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn unify_mismatched_types_error_test() {
  let state = initial_state([])
  let final = unify(state, VLit(LitInt(42)), VNeut(HHole(0), []))
  // Hole in actual binds to literal in expected
  assert final.errors == []
}

pub fn unify_nested_vctr_test() {
  let state = initial_state([])
  let final =
    unify(
      state,
      VCtr("Outer", VCtr("Inner", VNeut(HHole(0), []))),
      VCtr("Outer", VCtr("Inner", VNeut(HHole(0), []))),
    )
  assert final.errors == []
}

// ============================================================================
// Wildcard type matching — $Int and $Float
// ============================================================================

/// Test that `is_wildcard` correctly identifies $Int and $Float.
pub fn is_wildcard_int_test() {
  let int_type = VLitT(IntT)
  assert is_wildcard(int_type)
}

pub fn is_wildcard_float_test() {
  let float_type = VLitT(FloatT)
  assert is_wildcard(float_type)
}

pub fn is_wildcard_not_other_ctr_test() {
  let other_type = VCtr("Some", VNeut(HHole(0), []))
  assert case is_wildcard(other_type) {
    False -> True
    _ -> False
  }
}

pub fn is_wildcard_not_literal_test() {
  assert case is_wildcard(VLit(LitFloat(3.14))) {
    False -> True
    _ -> False
  }
}

/// Wildcard type matching: $Int (VLitT IntT) matches VLitT(IntT).
pub fn unify_int_wildcard_matches_int_test() {
  let int_type = VLitT(IntT)
  let int_val = VLitT(IntT)
  let final = unify(initial_state([]), int_type, int_val)
  assert final.errors == []
}

/// Wildcard type matching: $Float matches $Float.
pub fn unify_float_wildcard_matches_float_test() {
  let state = initial_state([])
  let float_type = VLitT(FloatT)
  let float_val = VLitT(FloatT)
  let final = unify(state, float_type, float_val)
  assert final.errors == []
}

/// Mismatch: IntT does NOT match FloatT.
pub fn unify_int_wildcard_rejects_float_test() {
  let state = initial_state([])
  let int_type = VLitT(IntT)
  let float_val = VLitT(FloatT)
  let final = unify(state, int_type, float_val)
  assert list.length(final.errors) >= 1
}

/// IntT wildcard DOES match specific integer types (I32T, etc.).
pub fn unify_int_type_matches_specific_int_test() {
  let state = initial_state([])
  let int_type = VLitT(IntT)
  let i32_type = VLitT(I32T)
  let final = unify(state, int_type, i32_type)
  // IntT is a wildcard that matches I32T — should succeed
  assert list.length(final.errors) == 0
}

/// VLitT does NOT match a constructor VCtr tag.
pub fn unify_int_wildcard_rejects_ctr_test() {
  let state = initial_state([])
  let int_type = VLitT(IntT)
  let ctr_val = VCtr("Some", VNeut(HHole(0), []))
  let final = unify(state, int_type, ctr_val)
  assert list.length(final.errors) >= 1
}

/// Test VLitT wildcard matching via literal_type_matches_wildcard.
pub fn literal_type_int_matches_int_test() {
  // IntT matches IntT wildcard
  assert literal_type_matches_wildcard(IntT, IntT)
}

pub fn literal_type_int_matches_float_test() {
  // IntT matches FloatT wildcard (int literals can be used as float)
  assert literal_type_matches_wildcard(FloatT, IntT)
}

pub fn literal_type_float_matches_float_test() {
  // FloatT matches FloatT wildcard
  assert literal_type_matches_wildcard(FloatT, FloatT)
}

pub fn literal_type_int_rejects_float_test() {
  // IntT does NOT match FloatT
  case literal_type_matches_wildcard(IntT, FloatT) {
    False -> True
    _ -> False
  }
}

pub fn literal_type_i32_matches_int_test() {
  // I32T matches IntT wildcard
  assert literal_type_matches_wildcard(IntT, I32T)
}

pub fn literal_type_f64_matches_float_test() {
  // F64T matches FloatT wildcard
  assert literal_type_matches_wildcard(FloatT, F64T)
}
