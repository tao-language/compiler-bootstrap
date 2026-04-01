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

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s = c.initial_state

const s1 = Span("eval_test", 1, 1, 1, 1)

const s2 = Span("eval_test", 2, 2, 2, 2)

fn typ(l, s) {
  c.Typ(l, s)
}

fn lit(v, s) {
  c.Lit(v, s)
}

fn litt(t, s) {
  c.LitT(t, s)
}

fn var(i, s) {
  c.Var(i, s)
}

fn hole(id, s) {
  c.Hole(id, s)
}

fn v32(v) {
  c.VLit(c.I32(v))
}

fn v64(v) {
  c.VLit(c.I64(v))
}

const v32t = c.VLitT(c.I32T)

const v64t = c.VLitT(c.I64T)

fn vhole(i) {
  c.VNeut(c.HHole(i), [])
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
  c.eval(c.ffi_build, [], typ(0, s1)) |> should.equal(c.VTyp(0))
  c.eval(c.ffi_build, [], typ(1, s1)) |> should.equal(c.VTyp(1))
}

// ============================================================================
// LITERAL EVALUATION
// ============================================================================

pub fn eval_lit_test() {
  c.eval(c.ffi_build, [], lit(c.I32(1), s1))
  |> should.equal(c.VLit(c.I32(1)))
  c.eval(c.ffi_build, [], lit(c.I64(1), s1))
  |> should.equal(c.VLit(c.I64(1)))
  c.eval(c.ffi_build, [], lit(c.U32(1), s1))
  |> should.equal(c.VLit(c.U32(1)))
  c.eval(c.ffi_build, [], lit(c.U64(1), s1))
  |> should.equal(c.VLit(c.U64(1)))
  c.eval(c.ffi_build, [], lit(c.F32(1.0), s1))
  |> should.equal(c.VLit(c.F32(1.0)))
  c.eval(c.ffi_build, [], lit(c.F64(1.0), s1))
  |> should.equal(c.VLit(c.F64(1.0)))
}

// ============================================================================
// LITERAL TYPE EVALUATION
// ============================================================================

pub fn eval_litt_test() {
  c.eval(c.ffi_build, [], litt(c.I32T, s1))
  |> should.equal(c.VLitT(c.I32T))
  c.eval(c.ffi_build, [], litt(c.I64T, s1))
  |> should.equal(c.VLitT(c.I64T))
  c.eval(c.ffi_build, [], litt(c.U32T, s1))
  |> should.equal(c.VLitT(c.U32T))
  c.eval(c.ffi_build, [], litt(c.U64T, s1))
  |> should.equal(c.VLitT(c.U64T))
  c.eval(c.ffi_build, [], litt(c.F32T, s1))
  |> should.equal(c.VLitT(c.F32T))
  c.eval(c.ffi_build, [], litt(c.F64T, s1))
  |> should.equal(c.VLitT(c.F64T))
}

// ============================================================================
// VARIABLE EVALUATION
// ============================================================================

pub fn eval_var_test() {
  let env = [v32(0)]
  c.eval(c.ffi_build, env, var(0, s1)) |> should.equal(v32(0))
  c.eval(c.ffi_build, env, var(1, s1)) |> should.equal(c.VErr)
}

// ============================================================================
// HOLE EVALUATION
// ============================================================================

pub fn eval_hole_test() {
  c.eval(c.ffi_build, [], hole(0, s1)) |> should.equal(vhole(0))
  c.eval(c.ffi_build, [], hole(1, s1)) |> should.equal(vhole(1))
}
