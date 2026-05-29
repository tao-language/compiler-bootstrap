/// Tests for the Infer module (Bidirectional Type Checking)
///
/// These tests verify core logic only:
/// - Variable lookup via context
/// - Hole generation (fresh ID allocation)
/// - Error handling (undefined vars)
/// - Default value checking in record types
///
/// Trivial data-pass-through tests (Lit, LitT, Typ, Ctr, Rcd, Call)
/// have been removed — they only verify data flows through, not logic.
import core/ast as ast
import core/context as ctx
import core/elaborate.{infer}
import core/literals as lit
import core/term as tm
import core/value as v
import gleam/option.{Some}
import gleeunit
import syntax/span as span

pub fn main() {
  gleeunit.main()
}

const s = span.Span("elaborate_test", 0, 0, 0, 0)
const s1 = span.Span("elaborate_test", 1, 1, 1, 1)
const s2 = span.Span("elaborate_test", 2, 2, 2, 2)

// ============================================================================
// Variable lookup — tests context.lookup logic
// ============================================================================

pub fn infer_var_defined_test() {
  let ctx0 = ctx.new_ctx(["x"], [], [v.int(42)], [], [], [], 0)
  let term = ast.AST(ast.Var("x"), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.Var(0)
  assert type_ == v.int(42)
}

pub fn infer_var_undefined_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let term = ast.AST(ast.Var("x"), s)
  let #(result, type_, state) = infer(ctx0, term)
  let expected = ctx.with_err(ctx0, ctx.VarUndefined("x", s))
  assert state == expected
  assert result == tm.Err
  assert type_ == v.Err
}

// ============================================================================
// Hole generation — tests context.new_hole logic
// ============================================================================

pub fn infer_hole_concrete_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 1)
  let term = ast.AST(ast.Hole(0), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx.new_ctx([], [], [], [], [], [], 2)
  assert result == tm.Hole(0)
  assert type_ == v.hole(1)
}

pub fn infer_hole_unknown_test() {
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 10)
  let term = ast.AST(ast.Hole(-1), s)
  let #(result, type_, state) = infer(ctx0, term)
  // -1 triggers recursive new_hole, producing fresh IDs 10, 11
  assert state == ctx.new_ctx([], [], [], [], [], [], 12)
  assert result == tm.Hole(10)
  assert type_ == v.hole(11)
}

// ============================================================================
// Default value checking in record types
// ============================================================================

pub fn infer_rcdt_default_value_checked_test() {
  // RcdT with a default value: type is $Int, default is 42 (Int) — OK
  let ctx0 = ctx.new_ctx([], [], [], [], [], [], 0)
  let type_int = ast.AST(ast.LitT(lit.IntT), s1)
  let default_val = ast.AST(ast.Lit(lit.Int(42)), s2)
  let term = ast.AST(ast.RcdT([#("x", type_int, Some(default_val))]), s)
  let #(result, type_, state) = infer(ctx0, term)
  assert state == ctx0
  assert result == tm.RcdT([
    #("x", tm.LitT(lit.IntT), Some(tm.Lit(lit.Int(42)))),
  ])
  assert type_ == v.Typ(0)
}

// Note: infer_lam, infer_pi, infer_fix, infer_app are currently `todo` in
// the source, so their logic tests are deferred until implementation.
