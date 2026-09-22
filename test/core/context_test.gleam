/// Tests for the context module — variable lookup, error handling, hole generation.
///
/// These tests verify the core logic of:
/// - `lookup`: finding variables by name and returning their DeBruijn index + type
/// - `with_err` / `with_err_list`: accumulating errors in context
/// - `new_hole`: generating fresh hole IDs
import core/context.{
  Context, lookup, new_ctx, new_hole, pop_trace, pop_vars, push_trace, push_var,
  push_var_opt, set_var, with_err, lookup_var,
}
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

// ============================================================================
// Binding management (push/pop/set, opt bindings, trace)
// ============================================================================

/// `push_var`/`pop_vars` keep value and type bindings in lockstep: the
/// innermost binding is found by `lookup_var`, and popping restores the
/// outer binding.
pub fn push_pop_var_lockstep_test() {
  let ctx0 =
    push_var(new_ctx, #("x", v.int(1), v.int_t))
    |> push_var(#("x", v.int(2), v.int_t))
    |> push_var(#("y", v.int(3), v.int_t))
  // The innermost `x` (the second push) shadows the first.
  assert lookup_var(ctx0, "x") == Some(#(v.int(2), v.int_t))
  assert lookup_var(ctx0, "y") == Some(#(v.int(3), v.int_t))
  let ctx1 = pop_vars(ctx0, 1)
  assert lookup_var(ctx1, "x") == Some(#(v.int(2), v.int_t))
  assert lookup_var(ctx1, "y") == None
  let ctx2 = pop_vars(ctx1, 2)
  assert ctx2.env == []
  assert ctx2.types == []
}

/// `set_var` on an existing (innermost) name rewrites that entry's value
/// and type in place; the order of the other bindings is preserved.
pub fn set_var_rewrites_innermost_test() {
  let ctx0 =
    push_var(new_ctx, #("a", v.int(1), v.int_t))
    |> push_var(#("b", v.int(2), v.int_t))
    |> set_var("a", v.int(9), v.int_t)
  assert lookup_var(ctx0, "a") == Some(#(v.int(9), v.int_t))
  assert lookup_var(ctx0, "b") == Some(#(v.int(2), v.int_t))
}

/// `push_var_opt` fills missing values and types with fresh (unsolved)
/// holes that captured the context's env at the push.
pub fn push_var_opt_fresh_holes_test() {
  let ctx0 = push_var(new_ctx, #("k", v.int(7), v.int_t))
  let ctx1 =
    push_var_opt(ctx0, #("x", None, Some(v.int_t)))
  let ctx2 =
    push_var_opt(ctx1, #("y", Some(v.int(1)), None))
  case lookup_var(ctx1, "x") {
    Some(#(val, typ)) -> {
      assert typ == v.int_t
      assert case val {
        v.Neut(v.NHole(env, Some(0))) -> env == [v.int(7)]
        _ -> False
      }
    }
    None -> panic as "x must be bound"
  }
  case lookup_var(ctx2, "y") {
    Some(#(val, typ)) -> {
      assert val == v.int(1)
      assert case typ {
        v.Neut(v.NHole(_, Some(1))) -> True
        _ -> False
      }
    }
    None -> panic as "y must be bound"
  }
}

/// Identical errors (same data, span and trace) are deduplicated by
/// `with_err`; distinct ones accumulate.
pub fn with_err_deduplicates_identical_test() {
  let ctx0 = new_ctx
  let ctx1 = with_err(ctx0, e.VarUndefined("a"), s)
  let ctx2 = with_err(ctx1, e.VarUndefined("a"), s)
  assert list.length(ctx2.errors) == 1
  let ctx3 = with_err(ctx2, e.VarUndefined("b"), s)
  assert list.length(ctx3.errors) == 2
}

/// Trace breadcrumbs push/pop around constructs: errors recorded inside
/// carry the breadcrumb, and the trace is restored afterwards.
pub fn push_pop_trace_test() {
  let ctx0 = push_trace(new_ctx, #("let", s))
  let ctx1 = with_err(ctx0, e.VarUndefined("a"), s)
  case ctx1.errors {
    [err, ..] -> {
      assert err.trace == [#("let", s)]
    }
    _ -> panic as "expected an error"
  }
  let ctx2 = pop_trace(ctx0)
  assert ctx2.trace == []
}

import gleam/list
