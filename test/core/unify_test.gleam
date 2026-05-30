/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Error handling for mismatches
/// - Constructor tag and argument unification
import core/context.{TypeMismatch, new_ctx} as ctx
import core/unify.{unify}
import core/value as v
import gleeunit
import syntax/span

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
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx == ctx0
}

pub fn unify_vtyp_type_mismatch_test() {
  let a = v.Typ(0)
  let b = v.Typ(1)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  assert ctx == ctx.with_err(ctx0, error)
}

// ============================================================================
// Literal value unification
// ============================================================================

pub fn unify_vlit_same_int_test() {
  let a = v.int(42)
  let b = v.int(42)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx == ctx0
}

pub fn unify_vlit_type_mismatch_test() {
  let a = v.int(1)
  let b = v.int(2)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  assert ctx == ctx.with_err(ctx0, error)
}

// ============================================================================
// Literal type unification
// ============================================================================

pub fn unify_litt_same_test() {
  let a = v.int_t
  let b = v.int_t
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx == ctx0
}

pub fn unify_litt_type_mismatch_test() {
  let a = v.int_t
  let b = v.float_t
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  assert ctx == ctx.with_err(ctx0, error)
}

// ============================================================================
// Constructor unification
// ============================================================================

pub fn unify_ctr_same_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.int_t)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx == ctx0
}

pub fn unify_ctr_tag_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("B", v.int_t)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  assert ctx == ctx.with_err(ctx0, error)
}

pub fn unify_ctr_arg_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.float_t)
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(v.int_t, s1), #(v.float_t, s2))
  assert ctx == ctx.with_err(ctx0, error)
}
// ============================================================================
// Record unification
// ============================================================================

// ============================================================================
// Record type unification
// ============================================================================

// ============================================================================
// Neutral variable unification
// ============================================================================

// ============================================================================
// Neutral hole unification
// ============================================================================

// ============================================================================
// Neutral application unification
// ============================================================================

// ============================================================================
// Neutral match unification
// ============================================================================

// ============================================================================
// Neutral call unification
// ============================================================================

// ============================================================================
// Lambda unification
// ============================================================================

// ============================================================================
// Pi type unification
// ============================================================================

// ============================================================================
// Fix-point unification
// ============================================================================

// ============================================================================
// Type definition unification
// ============================================================================

// ============================================================================
// Error unification
// ============================================================================
