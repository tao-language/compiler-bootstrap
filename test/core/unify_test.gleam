/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Hole solving with occur-check
/// - Neutral term unification with spines
/// - Record and record type unification
/// - Pi type unification
/// - Force-value integration (holes resolved before comparison)
/// - EMatch unification
import core/ast
import core/state.{SpineArityMismatch, SpineElimMismatch, State, TypeMismatch, new_state, with_err}
import core/unify.{unify}
import gleam/list
import core/utils
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)
const s2 = Span("unify_test", 2, 2, 2, 2)
const s3 = Span("unify_test", 3, 3, 3, 3)
const s4 = Span("unify_test", 4, 4, 4, 4)
const s5 = Span("unify_test", 5, 5, 5, 5)

// ============================================================================
// Helper values
// ============================================================================

/// A hole: VNeut(HHole(10), [])
fn hole10() -> ast.Value {
  ast.vhole(10, [])
}

/// A hole applied to another hole: VNeut(HHole(10), [EApp(vhole(20, s2)])]
fn hole10_applied_to_hole20() -> ast.Value {
  ast.VNeut(ast.HHole(10), [ast.EApp(ast.vhole(20, []), s2)])
}

/// A VNeut with HVar(0) applied to vint_t
fn hvar0_applied_vint_t() -> ast.Value {
  ast.VNeut(ast.HVar(0), [ast.EApp(ast.vint_t, s2)])
}

/// A VNeut with HVar(0) applied to vfloat_t
fn hvar0_applied_vfloat_t() -> ast.Value {
  ast.VNeut(ast.HVar(0), [ast.EApp(ast.vfloat_t, s2)])
}

/// A VNeut with EMatch spine
fn hvar0_with_ematch() -> ast.Value {
  let case_term = ast.Case(ast.PAny(s3), None, ast.Var(0, s3), s3)
  ast.VNeut(ast.HVar(0), [ast.EMatch([], [case_term], s3)])
}

// ============================================================================
// Existing tests (unchanged)
// ============================================================================

pub fn unify_type_mismatch_test() {
  let a = #(ast.VTyp(0), s1)
  let b = #(ast.VTyp(1), s2)
  let state = unify(new_state, a, b)
  assert state == with_err(new_state, TypeMismatch(a, b))
}

pub fn unify_vtyp_test() {
  let a = #(ast.VTyp(0), s1)
  let b = #(ast.VTyp(0), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vlit_test() {
  let a = #(ast.VLit(ast.Int(1)), s1)
  let b = #(ast.VLit(ast.Int(1)), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vlitt_test() {
  let a = #(ast.VLitT(ast.IntT), s1)
  let b = #(ast.VLitT(ast.IntT), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_same_test() {
  let a = #(ast.vvar(0, []), s1)
  let b = #(ast.vvar(0, []), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_different_head_test() {
  let a = #(ast.vvar(0, []), s1)
  let b = #(ast.vvar(1, []), s2)
  let state = unify(new_state, a, b)
  assert state == with_err(new_state, TypeMismatch(a, b))
}

pub fn unify_vneut_spine_arity_mismatch_test() {
  let a = #(ast.vvar(0, [ast.EApp(ast.vint_t, s2)]), s1)
  let b = #(ast.vvar(0, []), s3)
  let state = unify(new_state, a, b)
  let error = SpineArityMismatch([ast.EApp(ast.vint_t, s2)], [])
  assert state == with_err(new_state, error)
}

pub fn unify_vneut_spine_elim_mismatch_test() {
  let a = #(ast.vvar(0, [ast.EApp(ast.vint_t, s2)]), s1)
  let b = #(ast.vvar(0, [ast.EMatch([], [], s4)]), s3)
  let state = unify(new_state, a, b)
  let error =
    state.SpineElimMismatch(ast.EApp(ast.vint_t, s2), ast.EMatch([], [], s4))
  assert state == with_err(new_state, error)
}

pub fn unify_vneut_spine_type_mismatch_test() {
  let a = #(ast.vvar(0, [ast.EApp(ast.vint_t, s2)]), s1)
  let b = #(ast.vvar(0, [ast.EApp(ast.vfloat_t, s4)]), s3)
  let state = unify(new_state, a, b)
  let error = TypeMismatch(#(ast.vint_t, s2), #(ast.vfloat_t, s4))
  assert state == with_err(new_state, error)
}

pub fn unify_vneut_hole_a_test() {
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.vint_t, s2)
  let state = unify(new_state, a, b)
  assert state == State(..state, subst: [#(10, ast.vint_t)])
}

pub fn unify_vneut_hole_b_test() {
  let a = #(ast.vint_t, s1)
  let b = #(ast.vhole(10, []), s2)
  let state = unify(new_state, a, b)
  assert state == State(..state, subst: [#(10, ast.vint_t)])
}

// ============================================================================
// Occur-check tests
// ============================================================================

pub fn unify_hole_occurs_in_itself_test() {
  // A hole cannot be unified with a value containing itself.
  // This tests the occur-check: hole 10 is in the value.
  // Note: The occur-check prevents binding hole 10 to a value containing itself,
  // so the hole remains unsolved and no error is recorded.
  let v = ast.VNeut(ast.HHole(10), [ast.EApp(ast.vhole(10, []), s2)])
  let a = #(ast.vhole(10, []), s1)
  let b = #(v, s2)
  let state = unify(new_state, a, b)
  // Hole 10 should NOT be in the substitution (occur-check prevented binding).
  case utils.list_lookup(state.subst, 10) {
    None -> True
    Some(_) -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_hole_occurs_in_nested_vctr_test() {
  // A hole cannot be unified with VCtr(..., VNeut(HHole(10), ...)).
  let v = ast.VCtr("A", ast.VNeut(ast.HHole(10), [ast.EApp(ast.vint_t, s2)]))
  let a = #(ast.vhole(10, []), s1)
  let b = #(v, s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_hole_occurs_in_vpi_test() {
  // A hole cannot be unified with a VPi that contains it.
  let v = ast.VPi([], #("x", ast.vhole(10, [])), ast.vint_t)
  let a = #(ast.vhole(10, []), s1)
  let b = #(v, s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_hole_no_occur_check_succeeds_test() {
  // A hole CAN be unified with a value that does NOT contain it.
  let v = ast.VCtr("A", ast.vfloat_t)
  let a = #(ast.vhole(10, []), s1)
  let b = #(v, s2)
  let state = unify(new_state, a, b)
  // Should succeed with the substitution.
  assert state == State(..state, subst: [#(10, ast.VCtr("A", ast.vfloat_t))])
}

// ============================================================================
// Force-value integration tests
// ============================================================================

pub fn unify_both_sides_force_value_test() {
  // Both sides should be force-normalized before comparison.
  // If both contain the same solved hole, they should unify.
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.vint(42), s2)
  let state1 = unify(new_state, a, b)
  // hole 10 should be bound to vint(42)
  assert state1 == State(..state1, subst: [#(10, ast.vint(42))])

  // Now unify two holes that should both resolve to the same value.
  let a2 = #(ast.vhole(10, []), s1)
  let b2 = #(ast.vhole(20, []), s2)
  // First, pre-bind hole 10.
  let state_pre = State(..new_state, subst: [#(10, ast.vfloat_t)])
  let state = unify(state_pre, a2, b2)
  // hole 20 should be bound to vfloat_t (the solution for hole 10)
  // The order of substitutions may vary, so we just check that both are bound.
  let has_10 = case utils.list_lookup(state.subst, 10) { Some(v) -> v == ast.vfloat_t _ -> False }
  let has_20 = case utils.list_lookup(state.subst, 20) { Some(v) -> v == ast.vfloat_t _ -> False }
  assert has_10 == True
  assert has_20 == True
}

pub fn unify_pre_solved_hole_both_sides_test() {
  // Both sides have the same pre-solved hole. They should unify.
  let state_pre = State(..new_state, subst: [#(10, ast.vfloat_t)])
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.vhole(10, []), s2)
  let state = unify(state_pre, a, b)
  // Both should resolve to vfloat_t, so they unify.
  assert state == state_pre
}

pub fn unify_pre_solved_hole_different_values_test() {
  // Both sides have the same hole, but the hole is bound to a value
  // that doesn't match the other side.
  let state_pre = State(..new_state, subst: [#(10, ast.vint_t)])
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.vfloat_t, s2)
  let state = unify(state_pre, a, b)
  // vint_t != vfloat_t, so this should error.
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// VCtr unification tests
// ============================================================================

pub fn unify_vctr_same_test() {
  let a = #(ast.VCtr("A", ast.vint_t), s1)
  let b = #(ast.VCtr("A", ast.vint_t), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vctr_different_tag_test() {
  let a = #(ast.VCtr("A", ast.vint_t), s1)
  let b = #(ast.VCtr("B", ast.vint_t), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_vctr_nested_same_test() {
  let a = #(ast.VCtr("A", ast.VCtr("B", ast.vfloat_t)), s1)
  let b = #(ast.VCtr("A", ast.VCtr("B", ast.vfloat_t)), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

// ============================================================================
// Record unification tests
// ============================================================================

pub fn unify_vrcd_same_test() {
  let a = #(ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)]), s1)
  let b = #(ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)]), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vrcd_different_field_order_test() {
  // Same fields, different order — should fail because fields must match.
  let a = #(ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)]), s1)
  let b = #(ast.VRcd([#("y", ast.vfloat_t), #("x", ast.vint_t)]), s2)
  let state = unify(new_state, a, b)
  // Fields don't match by name+position, so this should error.
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_vrcd_missing_field_test() {
  let a = #(ast.VRcd([#("x", ast.vint_t)]), s1)
  let b = #(ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)]), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// Record type unification tests
// ============================================================================

pub fn unify_vrcdt_same_test() {
  let a = #(ast.VRcdT([#("x", ast.vint_t, None), #("y", ast.vfloat_t, Some(ast.vint(42)))]), s1)
  let b = #(ast.VRcdT([#("x", ast.vint_t, None), #("y", ast.vfloat_t, Some(ast.vint(42)))]), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vrcdt_different_field_test() {
  let a = #(ast.VRcdT([#("x", ast.vint_t, None)]), s1)
  let b = #(ast.VRcdT([#("x", ast.vint_t, Some(ast.vint(42)))]), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// Pi type unification tests
// ============================================================================

pub fn unify_vpi_same_test() {
  let a = #(ast.VPi([], #("x", ast.vint_t), ast.vfloat_t), s1)
  let b = #(ast.VPi([], #("x", ast.vint_t), ast.vfloat_t), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vpi_different_domain_test() {
  let a = #(ast.VPi([], #("x", ast.vint_t), ast.vfloat_t), s1)
  let b = #(ast.VPi([], #("x", ast.vint_t), ast.vint_t), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_vpi_with_implicits_same_test() {
  let a = #(ast.VPi([#("n", ast.vint_t)], #("x", ast.vint_t), ast.vfloat_t), s1)
  let b = #(ast.VPi([#("n", ast.vint_t)], #("x", ast.vint_t), ast.vfloat_t), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vpi_depends_on_param_test() {
  // (x: Int) -> VNeut(HVar(0), []) — codomain refers to x.
  // This should unify with itself.
  let codomain = ast.VNeut(ast.HVar(0), [])
  let a = #(ast.VPi([], #("x", ast.vint_t), codomain), s1)
  let b = #(ast.VPi([], #("x", ast.vint_t), codomain), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

// ============================================================================
// VTypeDef unification tests
// ============================================================================

pub fn unify_vdef_same_empty_test() {
  let a = #(ast.VTypeDef([], []), s1)
  let b = #(ast.VTypeDef([], []), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

// ============================================================================
// EMatch unification tests
// ============================================================================

pub fn unify_vneut_ematch_same_test() {
  // Two identical EMatch eliminators should unify.
  let case1 = ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)
  let case2 = ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)
  let a = #(ast.VNeut(ast.HVar(0), [ast.EMatch([], [case1], s1)]), s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EMatch([], [case2], s1)]), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_ematch_different_cases_test() {
  // Two EMatch with different cases should not unify.
  let case1 = ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)
  let case2 = ast.Case(ast.PAny(s2), None, ast.Var(1, s2), s2)
  let a = #(ast.VNeut(ast.HVar(0), [ast.EMatch([], [case1], s1)]), s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EMatch([], [case2], s1)]), s2)
  let state = unify(new_state, a, b)
  // The bodies differ (Var(0) vs Var(1)), so this should error.
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

pub fn unify_vneut_ematch_env_test() {
  // Two EMatch with different environments.
  let case1 = ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)
  let case2 = ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)
  let a = #(ast.VNeut(ast.HVar(0), [ast.EMatch([ast.vint_t], [case1], s1)]), s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EMatch([ast.vfloat_t], [case2], s1)]), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// EFix unification tests
// ============================================================================

pub fn unify_vneut_efix_same_test() {
  // Two identical EFix eliminators should unify.
  let body1 = ast.Lit(ast.Int(42), s1)
  let body2 = ast.Lit(ast.Int(42), s1)
  let a = #(ast.VNeut(ast.HVar(0), [ast.EFix([], body1)]), s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EFix([], body2)]), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_vneut_efix_different_body_test() {
  // Two EFix with different bodies should not unify.
  let a = #(ast.VNeut(ast.HVar(0), [ast.EFix([], ast.Lit(ast.Int(42), s1))]), s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EFix([], ast.Lit(ast.Int(99), s1))]), s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// VErr unification tests
// ============================================================================

pub fn unify_verr_same_test() {
  let a = #(ast.VErr, s1)
  let b = #(ast.VErr, s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_verr_vs_other_test() {
  let a = #(ast.VErr, s1)
  let b = #(ast.vint_t, s2)
  let state = unify(new_state, a, b)
  case state.errors {
    [TypeMismatch(_, _)] -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}

// ============================================================================
// Force-value with hole resolution in spines
// ============================================================================

pub fn unify_hole_in_spine_arg_test() {
  // VNeut(HVar(0), [EApp(vhole(10, s2)])]) should unify with
  // VNeut(HVar(0), [EApp(vint_t, s2)]) when hole 10 is pre-bound.
  let state_pre = State(..new_state, subst: [#(10, ast.vint_t)])
  let v = ast.VNeut(ast.HVar(0), [ast.EApp(ast.vhole(10, []), s2)])
  let a = #(v, s1)
  let b = #(ast.VNeut(ast.HVar(0), [ast.EApp(ast.vint_t, s2)]), s3)
  let state = unify(state_pre, a, b)
  assert state == state_pre
}

pub fn unify_hole_in_hcall_args_test() {
  // VNeut(HCall("f", [vhole(10, s2)]), []) should unify with
  // VNeut(HCall("f", [vint_t]), []) when hole 10 is pre-bound.
  let state_pre = State(..new_state, subst: [#(10, ast.vint_t)])
  let v = ast.VNeut(ast.HCall("f", [ast.vhole(10, [])]), [])
  let a = #(v, s1)
  let b = #(ast.VNeut(ast.HCall("f", [ast.vint_t]), []), s3)
  let state = unify(state_pre, a, b)
  assert state == state_pre
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn unify_empty_spines_test() {
  let a = #(ast.vvar(0, []), s1)
  let b = #(ast.vvar(0, []), s2)
  let state = unify(new_state, a, b)
  assert state == new_state
}

pub fn unify_hole_resolves_via_forced_value_test() {
  // A hole in one side should be resolved by force_value before unify.
  let state_pre = State(..new_state, subst: [#(10, ast.VCtr("A", ast.vfloat_t))])
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.VCtr("A", ast.vfloat_t), s2)
  let state = unify(state_pre, a, b)
  // Both should resolve to the same value, so unify succeeds.
  assert state == state_pre
}

pub fn unify_hole_resolved_to_neutral_test() {
  // A hole resolves to a VNeut, and we compare with another VNeut.
  let state_pre = State(..new_state, subst: [#(10, ast.vfloat_t)])
  let a = #(ast.vhole(10, []), s1)
  let b = #(ast.vfloat_t, s2)
  let state = unify(state_pre, a, b)
  assert state == state_pre
}

pub fn unify_hole_resolved_to_neutral_needs_force_test() {
  // A hole resolves to VNeut(HVar(0), [EApp(vint_t, s2)])
  // and we compare with another VNeut with the same spine.
  let neutral = ast.VNeut(ast.HVar(0), [ast.EApp(ast.vint_t, s2)])
  let state_pre = State(..new_state, subst: [#(10, neutral)])
  let a = #(ast.vhole(10, []), s1)
  let b = #(neutral, s2)
  let state = unify(state_pre, a, b)
  assert state == state_pre
}

pub fn unify_multiple_holes_same_id_in_both_sides_test() {
  // Both sides have the same hole. It should be bound once to the first resolved value.
  let v = ast.VRcd([#("x", ast.vhole(10, [])), #("y", ast.vhole(10, []))])
  let a = #(v, s1)
  let b = #(ast.VRcd([#("x", ast.vint(1)), #("y", ast.vint(1))]), s2)
  let state = unify(new_state, a, b)
  // Hole 10 should be bound to vint(1) (from the first field unification).
  // The second field uses the substitution, so it also becomes vint(1).
  case utils.list_lookup(state.subst, 10) {
    Some(ast.VLit(ast.Int(1))) -> True
    _ -> False
  }
  |> fn(result) { assert result == True }
}
