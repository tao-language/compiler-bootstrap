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
import core/context.{new_ctx}
import core/infer.{infer}
import core/term as tm
import core/value as v
import gleeunit
import syntax/span

pub fn main() {
  gleeunit.main()
}

const s = span.Span("", 0, 0, 0, 0)

const s1 = span.Span("", 1, 1, 1, 1)

// ============================================================================
//  Typ
// ============================================================================

// ============================================================================
//  Hole
// ============================================================================

// ============================================================================
//  Lit
// ============================================================================

// ============================================================================
//  LitT
// ============================================================================

// ============================================================================
//  Var
// ============================================================================

pub fn infer_var_defined_test() {
  let ast = ast.var("x", s)
  let ctx0 = context.push_var(new_ctx, #("x", v.int(42), v.int_t))
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.Var(0)
  assert type_ == v.int_t
}

pub fn infer_var_undefined_test() {
  let ast = ast.var("x", s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == [context.VarUndefined("x", s)]
  assert result == tm.Err
  assert type_ == v.Err
}

// ============================================================================
//  Ctr
// ============================================================================

// ============================================================================
//  Rcd
// ============================================================================

// ============================================================================
//  RcdT
// ============================================================================

// ============================================================================
//  Call
// ============================================================================

// ============================================================================
//  Ann
// ============================================================================

// ============================================================================
//  Lam
// ============================================================================

pub fn infer_lam_simple_test() {
  // $fn(x: $Int) => x
  let ast = ast.lam(False, #("x", ast.int_t(s)), ast.var("x", s), s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], False, #("x", v.int_t), tm.int_t)
}

pub fn infer_lam_implicit_test() {
  // $fn<x: $Int> => x
  let ast = ast.lam(True, #("x", ast.int_t(s)), ast.var("x", s), s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(0))
  assert type_ == v.Pi([], True, #("x", v.int_t), tm.int_t)
}

pub fn infer_lam_closure_test() {
  // $let y = 3.14; $fn(x: $Int) => y
  let ast = ast.lam(False, #("x", ast.int_t(s)), ast.var("y", s), s)
  let ctx0 = context.push_var(new_ctx, #("y", v.float(3.14), v.float_t))
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.Lam(#("x", tm.int_t), tm.Var(1))
  assert type_ == v.Pi([v.float(3.14)], False, #("x", v.int_t), tm.float_t)
}

pub fn infer_lam_identity_test() {
  // $fn<a: $Type>(x: a) => x
  let ast =
    ast.lam(
      True,
      #("a", ast.typ(0, s)),
      ast.lam(False, #("x", ast.var("a", s)), ast.var("x", s), s),
      s,
    )
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
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

pub fn infer_lam_typeof_test() {
  // $fn<a: $Type>(x: a) => a
  let ast =
    ast.lam(
      True,
      #("a", ast.typ(0, s)),
      ast.lam(False, #("x", ast.var("a", s)), ast.var("a", s), s),
      s,
    )
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result
    == tm.Lam(#("a", tm.Typ(0)), tm.Lam(#("x", tm.Var(0)), tm.Var(1)))
  assert type_
    == v.Pi(
      [],
      True,
      #("a", v.Typ(0)),
      tm.Pi(False, #("x", tm.Var(0)), tm.Typ(0)),
    )
}

// ============================================================================
//  Pi
// ============================================================================

// ============================================================================
//  Fix
// ============================================================================

// ============================================================================
//  App
// ============================================================================

pub fn infer_app_error_not_a_function_test() {
  let #(_implicit, explicit) = #(True, False)
  let ast = ast.app(explicit, ast.float(3.14, s1), ast.int(1, s), s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == [context.NotAFunction(tm.float(3.14), v.float_t, s1)]
  assert result == tm.Err
  assert type_ == v.Err
}

pub fn infer_app_explicit_arg_test() {
  let #(_implicit, explicit) = #(True, False)
  let ast = ast.app(explicit, ast.var("f", s), ast.int(42, s), s)
  let pi = v.Pi([], explicit, #("x", v.int_t), tm.Var(0))
  let ctx0 = context.push_var(new_ctx, #("f", v.var(0), pi))
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.App(tm.Var(0), tm.int(42))
  assert type_ == v.int(42)
}

pub fn infer_app_implicit_arg_test() {
  let #(implicit, _explicit) = #(True, False)
  let ast = ast.app(implicit, ast.var("f", s), ast.int(42, s), s)
  let pi = v.Pi([], implicit, #("a", v.int_t), tm.Var(0))
  let ctx0 = context.push_var(new_ctx, #("f", v.var(0), pi))
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.App(tm.Var(0), tm.int(42))
  assert type_ == v.int(42)
}

pub fn infer_app_error_expected_explicit_argument_test() {
  let #(implicit, explicit) = #(True, False)
  let ast = ast.app(implicit, ast.var("f", s), ast.int(42, s), s1)
  let pi = v.Pi([], explicit, #("x", v.int_t), tm.Var(0))
  let ctx0 = context.push_var(new_ctx, #("f", v.var(0), pi))
  let #(result, type_, ctx) = infer(ctx0, ast)
  let error = context.AppExpectedExplicitArg(pi, s1)
  assert ctx.errors == [error]
  assert result == tm.Err
  assert type_ == v.Err
}

pub fn infer_app_implicit_expansion_test() {
  let #(implicit, explicit) = #(True, False)
  let ast = ast.app(explicit, ast.var("f", s), ast.int(42, s), s)
  let pi = v.Pi([], implicit, #("a", v.Typ(0)), tm.Var(0))
  let ctx0 = context.push_var(new_ctx, #("f", v.var(0), pi))
  let #(result, type_, ctx) = infer(ctx0, ast)
  let error = context.NotAFunction(tm.App(tm.Var(0), tm.Hole(0)), v.hole(0), s)
  assert ctx.errors == [error]
  assert result == tm.Err
  assert type_ == v.Err
}

pub fn infer_app_implicit_solve_hole_test() {
  let #(implicit, explicit) = #(True, False)
  let ast = ast.app(explicit, ast.var("identity", s), ast.int(1, s), s)
  let pi =
    v.Pi(
      [],
      implicit,
      #("a", v.Typ(0)),
      tm.Pi(explicit, #("x", tm.Var(0)), tm.Var(1)),
    )
  let ctx0 = context.push_var(new_ctx, #("identity", v.var(0), pi))
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.App(tm.App(tm.Var(0), tm.Hole(0)), tm.int(1))
  assert type_ == v.int_t
}

// ============================================================================
//  TypeDef
// ============================================================================

// ============================================================================
//  Let
// ============================================================================

// ============================================================================
//  Match
// ============================================================================

// ============================================================================
//  Err
// ============================================================================

pub fn infer_err_test() {
  let ast = ast.err(s)
  let ctx0 = new_ctx
  let #(result, type_, ctx) = infer(ctx0, ast)
  assert ctx.errors == []
  assert result == tm.Err
  assert type_ == v.Err
}
