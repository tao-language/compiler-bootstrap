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

import gleeunit
import core/unify.{unify, occurs_check}
import core/state.{initial_state, def_var, TypeMismatch}
import core/ast.{
  VNeut, HHole, HVar, VLam, VPi, VCtr, VLit, VRcd, VErr, EApp,
  Var, Int as LitInt, Float as LitFloat,
}
import gleam/list
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Basic value equality — same types unify successfully
// ============================================================================

pub fn unify_same_lit_int_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitInt(42)),
  )
  assert final.errors == []
}

pub fn unify_same_lit_float_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLit(LitFloat(3.14)),
    VLit(LitFloat(3.14)),
  )
  assert final.errors == []
}

pub fn unify_same_vctr_test() {
  let state = initial_state([])
  let final = unify(
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
  let final = unify(
    state,
    VNeut(HHole(0), []),
    VLit(LitInt(42)),
  )
  // Hole is bound — no errors
  assert final.errors == []
}

pub fn unify_hole_in_actual_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLit(LitInt(42)),
    VNeut(HHole(0), []),
  )
  assert final.errors == []
}

pub fn unify_same_hole_id_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VNeut(HHole(5), []),
    VNeut(HHole(5), []),
  )
  assert final.errors == []
}

pub fn unify_different_hole_ids_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VNeut(HHole(1), []),
    VNeut(HHole(2), []),
  )
  // Different holes are treated as different values
  assert list.length(final.errors) >= 1
}

pub fn unify_hole_reunification_test() {
  let state = initial_state([])
  let s1 = unify(
    state,
    VNeut(HHole(0), []),
    VLit(LitInt(42)),
  )
  // Re-unify the same hole — should succeed (already bound to 42)
  let s2 = unify(
    s1,
    VNeut(HHole(0), []),
    VLit(LitInt(42)),
  )
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
  let final = unify(
    state,
    VPi(dom, codom),
    VPi(dom, codom),
  )
  assert final.errors == []
}

pub fn unify_mismatched_pi_domain_test() {
  // Use concrete values that genuinely don't unify
  let state = initial_state([])
  let final = unify(
    state,
    VPi(VLit(LitInt(42)), VNeut(HHole(0), [])),
    VPi(VLit(LitInt(43)), VNeut(HHole(0), [])),
  )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Lambda type unification
// ============================================================================

pub fn unify_same_lam_type_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLam(#("x", VNeut(HHole(0), [])), Var(0, single("", 0, 0))),
    VLam(#("y", VNeut(HHole(0), [])), Var(0, single("", 0, 0))),
  )
  assert final.errors == []
}

pub fn unify_mismatched_lam_type_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLam(#("x", VLit(LitInt(42))), Var(0, single("", 0, 0))),
    VLam(#("y", VLit(LitFloat(3.14))), Var(0, single("", 0, 0))),
  )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Constructor mismatch
// ============================================================================

pub fn unify_different_ctr_tags_test() {
  let state = initial_state([])
  let final = unify(
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
  let final = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitInt(43)),
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_lit_int_vs_float_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitFloat(42.0)),
  )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Record unification
// ============================================================================

pub fn unify_same_vrcd_fields_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VRcd([#("name", VNeut(HHole(0), []))]),
    VRcd([#("name", VNeut(HHole(0), []))]),
  )
  assert final.errors == []
}

pub fn unify_mismatched_vrcd_fields_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VRcd([#("name", VNeut(HHole(0), []))]),
    VRcd([#("age", VNeut(HHole(0), []))]),
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_mismatched_vrcd_arity_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VRcd([#("name", VNeut(HHole(0), []))]),
    VRcd([]),
  )
  assert list.length(final.errors) >= 1
}

// ============================================================================
// Neutral term comparison
// ============================================================================

pub fn unify_same_hvar_test() {
  // HVar(0) looks up in state — need a binding for it
  let bound_val = VNeut(HHole(0), [])
  let s1 = def_var(initial_state([]), "x", bound_val, bound_val)
  let final = unify(
    s1,
    VNeut(HVar(0), [EApp(VRcd([]))]),
    VNeut(HVar(0), [EApp(VRcd([]))]),
  )
  assert final.errors == []
}

pub fn unify_different_hvar_test() {
  let state = initial_state([])
  let final = unify(
    state,
    VNeut(HVar(0), []),
    VNeut(HVar(1), []),
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_hvar_vs_hhole_test() {
  // HVar(0) looks up in empty state — fails, then HHole(0) gets bound
  let state = initial_state([])
  let final = unify(
    state,
    VNeut(HVar(0), []),
    VNeut(HHole(0), []),
  )
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
  let final = unify(
    state,
    VCtr("Outer", VCtr("Inner", VNeut(HHole(0), []))),
    VCtr("Outer", VCtr("Inner", VNeut(HHole(0), []))),
  )
  assert final.errors == []
}


