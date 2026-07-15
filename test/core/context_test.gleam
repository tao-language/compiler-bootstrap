/// Tests for the context module — variable lookup, error handling, hole generation.
///
/// These tests verify the core logic of:
/// - `lookup`: finding variables by name and returning their DeBruijn index + type
/// - `with_err` / `with_err_list`: accumulating errors in context
/// - `new_hole`: generating fresh hole IDs
import core/context.{Context, lookup, new_ctx, new_hole, with_err}
import core/error as e
import core/value as v
import gleam/option.{None, Some}
import syntax/span

const s = span.Span("context_test", 0, 0, 0, 0)

// ============================================================================
// Variable lookup
// ============================================================================

pub fn lookup_finds_first_variable_test() {
  let ctx0 = Context(..new_ctx, types: [#("x", v.int_t), #("y", v.float_t)])
  assert lookup(ctx0, "x") == Some(#(0, v.int_t))
}

pub fn lookup_finds_second_variable_test() {
  let ctx0 = Context(..new_ctx, types: [#("x", v.int_t), #("y", v.float_t)])
  assert lookup(ctx0, "y") == Some(#(1, v.float_t))
}

pub fn lookup_undefined_variable_test() {
  let ctx0 = Context(..new_ctx, types: [#("x", v.int_t), #("y", v.float_t)])
  assert lookup(ctx0, "z") == None
}

pub fn lookup_empty_context_test() {
  let ctx0 = new_ctx
  assert lookup(ctx0, "x") == None
}

// ============================================================================
// Error accumulation
// ============================================================================

pub fn with_err_appends_to_existing_errors_test() {
  let ctx0 = new_ctx
  let ctx1 = with_err(ctx0, e.VarUndefined("a"), s)
  let ctx2 = with_err(ctx1, e.VarUndefined("b"), s)
  // Should have 2 errors, not replace the first (with_err prepends, so reverse order)
  assert ctx2.errors
    == [
      e.Error(e.VarUndefined("b"), s, []),
      e.Error(e.VarUndefined("a"), s, []),
    ]
}

// ============================================================================
// Hole generation
// ============================================================================

pub fn new_hole_fresh_id_test() {
  let ctx0 = new_ctx
  let #(id1, ctx1) = new_hole(ctx0)
  let #(id2, ctx2) = new_hole(ctx1)
  assert id1 == 0
  assert id2 == 1
  // hole_counter advanced: ctx1 has 1, ctx2 has 2
  assert ctx1.hole_counter == 1
  assert ctx2.hole_counter == 2
}

pub fn new_hole_increments_monotonically_test() {
  let ctx0 = Context(..new_ctx, hole_counter: 100)
  let #(id1, ctx1) = new_hole(ctx0)
  let #(id2, ctx2) = new_hole(ctx1)
  let #(id3, ctx3) = new_hole(ctx2)
  assert id1 == 100
  assert id2 == 101
  assert id3 == 102
  assert ctx3.hole_counter == 103
}
