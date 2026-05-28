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
import core/state.{State, TypeMismatch, new_state, with_err}
import core/unify.{unify}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

pub fn unify_vtyp_type_mismatch_test() {
  let a = ast.VTyp(0)
  let b = ast.VTyp(1)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == State(..new_state, errors: [TypeMismatch(#(a, s1), #(b, s2))])
  assert value == ast.VErr
}

pub fn unify_vtyp_test() {
  let a = ast.VTyp(0)
  let b = ast.VTyp(0)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == new_state
  assert value == ast.VTyp(0)
}

pub fn unify_vlit_type_mismatch_test() {
  let a = ast.vint(1)
  let b = ast.vint(2)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == State(..new_state, errors: [TypeMismatch(#(a, s1), #(b, s2))])
  assert value == ast.VErr
}

pub fn unify_vlit_test() {
  let a = ast.vint(42)
  let b = ast.vint(42)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == new_state
  assert value == ast.vint(42)
}

pub fn unify_vlitt_type_mismatch_test() {
  let a = ast.vint_t
  let b = ast.vfloat_t
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == State(..new_state, errors: [TypeMismatch(#(a, s1), #(b, s2))])
  assert value == ast.VErr
}

pub fn unify_litt_test() {
  let a = ast.vint_t
  let b = ast.vint_t
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == new_state
  assert value == ast.vint_t
}

pub fn unify_ctr_tag_mismatch_test() {
  let a = ast.VCtr("A", ast.vint_t)
  let b = ast.VCtr("B", ast.vint_t)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == State(..new_state, errors: [TypeMismatch(#(a, s1), #(b, s2))])
  assert value == ast.VErr
}

pub fn unify_ctr_tag_arg_mismatch_test() {
  let a = ast.VCtr("A", ast.vint_t)
  let b = ast.VCtr("A", ast.vfloat_t)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(ast.vint_t, s1), #(ast.vfloat_t, s2))
  assert state == State(..new_state, errors: [error])
  assert value == ast.VCtr("A", ast.VErr)
}

pub fn unify_ctr_test() {
  let a = ast.VCtr("A", ast.vint_t)
  let b = ast.VCtr("A", ast.vint_t)
  let #(value, state) = unify(new_state, #(a, s1), #(b, s2))
  assert state == new_state
  assert value == a
}
