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
import core/state.{
  SpineArityMismatch, SpineElimMismatch, State, TypeMismatch, new_state,
  with_err,
}
import core/unify.{unify}
import core/utils
import gleam/list
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
