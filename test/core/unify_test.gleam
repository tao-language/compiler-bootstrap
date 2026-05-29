/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Error handling for mismatches
/// - Constructor tag and argument unification
import core/context.{TypeMismatch, with_err} as ctx
import core/unify.{unify}
import core/value as v
import gleeunit
import syntax/span as span

pub fn main() {
  gleeunit.main()
}

const s1 = span.Span("unify_test", 1, 1, 1, 1)
const s2 = span.Span("unify_test", 2, 2, 2, 2)

// ============================================================================
// Typ (universe level) unification
// ============================================================================

pub fn unify_vtyp_same_universe_test() {
  let a = v.Typ(0)
  let b = v.Typ(0)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  assert state == ctx0
  assert value == v.Typ(0)
}

pub fn unify_vtyp_type_mismatch_test() {
  let a = v.Typ(0)
  let b = v.Typ(1)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx0, error)
  assert state == expected
  assert value == v.Err
}

// ============================================================================
// Literal value unification
// ============================================================================

pub fn unify_vlit_same_int_test() {
  let a = v.int(42)
  let b = v.int(42)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  assert state == ctx0
  assert value == v.int(42)
}

pub fn unify_vlit_type_mismatch_test() {
  let a = v.int(1)
  let b = v.int(2)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx0, error)
  assert state == expected
  assert value == v.Err
}

// ============================================================================
// Literal type unification
// ============================================================================

pub fn unify_litt_same_test() {
  let a = v.int_t
  let b = v.int_t
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  assert state == ctx0
  assert value == v.int_t
}

pub fn unify_litt_type_mismatch_test() {
  let a = v.int_t
  let b = v.float_t
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx0, error)
  assert state == expected
  assert value == v.Err
}

// ============================================================================
// Constructor unification
// ============================================================================

pub fn unify_ctr_same_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.int_t)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  assert state == ctx0
  assert value == a
}

pub fn unify_ctr_tag_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("B", v.int_t)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx0, error)
  assert state == expected
  assert value == v.Err
}

pub fn unify_ctr_arg_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.float_t)
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(v.int_t, s1), #(v.float_t, s2))
  let expected = with_err(ctx0, error)
  assert state == expected
  assert value == v.Ctr("A", v.Err)
}
