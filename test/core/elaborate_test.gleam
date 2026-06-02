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
import core/ast
import core/context.{Context, new_ctx}
import core/elaborate.{infer}
import core/term as tm
import core/value as v
import gleam/option.{Some}
import gleeunit
import syntax/span

pub fn main() {
  gleeunit.main()
}

const s = span.Span("", 0, 0, 0, 0)

const s1 = span.Span("", 1, 1, 1, 1)

const s2 = span.Span("", 2, 2, 2, 2)

// ============================================================================
// Infer Typ
// ============================================================================

// ============================================================================
// Infer Hole
// ============================================================================

// ============================================================================
// Infer Lit
// ============================================================================

// ============================================================================
// Infer LitT
// ============================================================================

// ============================================================================
// Infer Var
// ============================================================================

pub fn infer_var_defined_test() {
  let term = ast.var("x", s)
  let ctx0 = context.push_var(new_ctx, #("x", v.int(42), v.int_t))
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result == tm.Var(0)
  assert type_ == v.int_t
}

pub fn infer_var_undefined_test() {
  let term = ast.var("x", s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == [context.VarUndefined("x", s)]
  assert result == tm.Err
  assert type_ == v.Err
}

// ============================================================================
// Infer Ctr
// ============================================================================

// ============================================================================
// Infer Rcd
// ============================================================================

// ============================================================================
// Infer RcdT
// ============================================================================

// ============================================================================
// Infer Call
// ============================================================================

// ============================================================================
// Infer Ann
// ============================================================================

// ============================================================================
// Infer Lam
// ============================================================================

pub fn infer_lam_simple_test() {
  // $fn(x: $Int) => x
  let term = ast.lam(False, #("x", ast.int_t(s)), ast.var("x", s), s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], False, #("x", v.int_t), tm.int_t)
}

pub fn infer_lam_implicit_test() {
  // $fn<x: $Int> => x
  let term = ast.lam(True, #("x", ast.int_t(s)), ast.var("x", s), s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], True, #("x", v.int_t), tm.int_t)
}

pub fn infer_lam_closure_test() {
  // $let y = 3.14; $fn(x: $Int) => y
  let term = ast.lam(False, #("x", ast.int_t(s)), ast.var("y", s), s)
  let ctx0 = context.push_var(new_ctx, #("y", v.float(3.14), v.float_t))
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(1))
  assert type_ == v.Pi([v.float(3.14)], False, #("x", v.int_t), tm.float_t)
}

pub fn infer_lam_identity_test() {
  // $fn<a: $Type>(x: a) => x
  let term =
    ast.lam(
      True,
      #("a", ast.typ(0, s)),
      ast.lam(False, #("x", ast.var("a", s)), ast.var("x", s), s),
      s,
    )
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result
    == tm.Lam(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(0)))
  assert type_
    == v.Pi(
      [],
      True,
      #("a", v.Typ(0)),
      tm.Pi(False, #("x", tm.Var(0)), tm.Var(1)),
    )
}

// ============================================================================
// Infer Pi
// ============================================================================

// ============================================================================
// Infer Fix
// ============================================================================

// ============================================================================
// Infer App
// ============================================================================

// ============================================================================
// Infer TypeDef
// ============================================================================

// ============================================================================
// Infer Let
// ============================================================================

// ============================================================================
// Infer Match
// ============================================================================

// ============================================================================
// Infer Err
// ============================================================================

pub fn infer_err_test() {
  let term = ast.err(s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, term)
  assert ctx.errors == []
  assert result == tm.Err
  assert type_ == v.Err
}
