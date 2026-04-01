// ============================================================================
// EVALUATION TESTS
// ============================================================================
/// Tests for the evaluator.
///
/// Evaluation reduces terms to values in a given environment.
/// It's used for:
/// - Runtime execution
/// - Normalization by evaluation
/// - Comptime evaluation
import core/ast as ast
import core/state as state
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/eval.{eval}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

fn get_s() { state.initial_state() }

const s1 = Span("eval_test", 1, 1, 1, 1)

const s2 = Span("eval_test", 2, 2, 2, 2)

fn typ(l, s) {
  ast.Typ(l, s)
}

fn lit(v, s) {
  ast.Lit(v, s)
}

fn litt(t, s) {
  ast.LitT(t, s)
}

fn var(i, s) {
  ast.Var(i, s)
}

fn hole(id, s) {
  ast.Hole(id, s)
}

fn v32(v) {
  ast.VLit(ast.I32(v))
}

fn v64(v) {
  ast.VLit(ast.I64(v))
}

const v32t = ast.VLitT(ast.I32T)

const v64t = ast.VLitT(ast.I64T)

fn vhole(i) {
  ast.VNeut(ast.HHole(i), [])
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

pub fn range_test() {
  c.range(0, 0, 1) |> should.equal([])
  c.range(0, 1, 1) |> should.equal([0])
  c.range(0, 2, 1) |> should.equal([0, 1])
  c.range(0, 3, 1) |> should.equal([0, 1, 2])
}

// ============================================================================
// TYPE EVALUATION
// ============================================================================

pub fn eval_typ_test() {
  eval(c.ffi_build, [], typ(0, s1)) |> should.equal(ast.VTyp(0))
  eval(c.ffi_build, [], typ(1, s1)) |> should.equal(ast.VTyp(1))
}

// ============================================================================
// LITERAL EVALUATION
// ============================================================================

pub fn eval_lit_test() {
  eval(c.ffi_build, [], lit(ast.I32(1), s1))
  |> should.equal(ast.VLit(ast.I32(1)))
  eval(c.ffi_build, [], lit(ast.I64(1), s1))
  |> should.equal(ast.VLit(ast.I64(1)))
  eval(c.ffi_build, [], lit(ast.U32(1), s1))
  |> should.equal(ast.VLit(ast.U32(1)))
  eval(c.ffi_build, [], lit(ast.U64(1), s1))
  |> should.equal(ast.VLit(ast.U64(1)))
  eval(c.ffi_build, [], lit(ast.F32(1.0), s1))
  |> should.equal(ast.VLit(ast.F32(1.0)))
  eval(c.ffi_build, [], lit(ast.F64(1.0), s1))
  |> should.equal(ast.VLit(ast.F64(1.0)))
}

// ============================================================================
// LITERAL TYPE EVALUATION
// ============================================================================

pub fn eval_litt_test() {
  eval(c.ffi_build, [], litt(ast.I32T, s1))
  |> should.equal(ast.VLitT(ast.I32T))
  eval(c.ffi_build, [], litt(ast.I64T, s1))
  |> should.equal(ast.VLitT(ast.I64T))
  eval(c.ffi_build, [], litt(ast.U32T, s1))
  |> should.equal(ast.VLitT(ast.U32T))
  eval(c.ffi_build, [], litt(ast.U64T, s1))
  |> should.equal(ast.VLitT(ast.U64T))
  eval(c.ffi_build, [], litt(ast.F32T, s1))
  |> should.equal(ast.VLitT(ast.F32T))
  eval(c.ffi_build, [], litt(ast.F64T, s1))
  |> should.equal(ast.VLitT(ast.F64T))
}

// ============================================================================
// VARIABLE EVALUATION
// ============================================================================

pub fn eval_var_test() {
  let env = [v32(0)]
  eval(c.ffi_build, env, var(0, s1)) |> should.equal(v32(0))
  eval(c.ffi_build, env, var(1, s1)) |> should.equal(ast.VErr)
}

// ============================================================================
// HOLE EVALUATION
// ============================================================================

pub fn eval_hole_test() {
  eval(c.ffi_build, [], hole(0, s1)) |> should.equal(vhole(0))
  eval(c.ffi_build, [], hole(1, s1)) |> should.equal(vhole(1))
}
