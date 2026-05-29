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
import core/context.{type Context, TypeMismatch, with_err}
import core/unify.{unify}
import core/value.{type Value} as v
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

pub fn unify_vtyp_type_mismatch_test() {
  let a = v.Typ(0)
  let b = v.Typ(1)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx, error)
  assert state == expected
  assert value == v.Err
}

pub fn unify_vtyp_test() {
  let a = v.Typ(0)
  let b = v.Typ(0)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  assert state == ctx
  assert value == v.Typ(0)
}

pub fn unify_vlit_type_mismatch_test() {
  let a = v.int(1)
  let b = v.int(2)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx, error)
  assert state == expected
  assert value == v.Err
}

pub fn unify_vlit_test() {
  let a = v.int(42)
  let b = v.int(42)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  assert state == ctx
  assert value == v.int(42)
}

pub fn unify_vlitt_type_mismatch_test() {
  let a = v.int_t
  let b = v.float_t
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx, error)
  assert state == expected
  assert value == v.Err
}

pub fn unify_litt_test() {
  let a = v.int_t
  let b = v.int_t
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  assert state == ctx
  assert value == v.int_t
}

pub fn unify_ctr_tag_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("B", v.int_t)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(a, s1), #(b, s2))
  let expected = with_err(ctx, error)
  assert state == expected
  assert value == v.Err
}

pub fn unify_ctr_tag_arg_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.float_t)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  let error = TypeMismatch(#(v.int_t, s1), #(v.float_t, s2))
  let expected = with_err(ctx, error)
  assert state == expected
  assert value == v.Ctr("A", v.Err)
}

pub fn unify_ctr_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.int_t)
  let ctx = context.new_ctx([], [], [], [], [], [], 0)
  let #(value, state) = unify(ctx, #(a, s1), #(b, s2))
  assert state == ctx
  assert value == a
}
