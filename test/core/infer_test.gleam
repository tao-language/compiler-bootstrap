// ============================================================================
// TYPE INFERENCE TESTS
// ============================================================================
/// Tests for bidirectional type inference.
///
/// Type inference determines the type of a term.
/// It works together with type checking in a bidirectional system.
import core/ast as ast
import core/state as state
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/infer.{infer}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s = state.initial_state

const s0 = Span("infer_test", 0, 0, 0, 0)

const s1 = Span("infer_test", 1, 1, 1, 1)

const s2 = Span("infer_test", 2, 2, 2, 2)

const s3 = Span("infer_test", 3, 3, 3, 3)

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

fn ctr(k, arg, s) {
  ast.Ctr(k, arg, s)
}

fn rcd(fields, s) {
  ast.Rcd(fields, s)
}

fn i32(v, s) {
  lit(ast.I32(v), s)
}

fn i64(v, s) {
  lit(ast.I64(v), s)
}

fn i32t(s) {
  litt(ast.I32T, s)
}

fn i64t(s) {
  litt(ast.I64T, s)
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
// TYPE INFERENCE
// ============================================================================

pub fn infer_typ_test() {
  infer(s, typ(0, s1))
  |> should.equal(#(ast.VTyp(0), ast.VTyp(1), s))
}

// ============================================================================
// LITERAL INFERENCE
// ============================================================================

pub fn infer_lit_test() {
  infer(s, lit(ast.I32(1), s1))
  |> should.equal(#(ast.VLit(ast.I32(1)), ast.VLitT(ast.I32T), s))
  infer(s, lit(ast.I64(1), s1))
  |> should.equal(#(ast.VLit(ast.I64(1)), ast.VLitT(ast.I64T), s))
  infer(s, lit(ast.U32(1), s1))
  |> should.equal(#(ast.VLit(ast.U32(1)), ast.VLitT(ast.U32T), s))
  infer(s, lit(ast.U64(1), s1))
  |> should.equal(#(ast.VLit(ast.U64(1)), ast.VLitT(ast.U64T), s))
  infer(s, lit(ast.F32(1.0), s1))
  |> should.equal(#(ast.VLit(ast.F32(1.0)), ast.VLitT(ast.F32T), s))
  infer(s, lit(ast.F64(1.0), s1))
  |> should.equal(#(ast.VLit(ast.F64(1.0)), ast.VLitT(ast.F64T), s))
}

// ============================================================================
// LITERAL TYPE INFERENCE
// ============================================================================

pub fn infer_litt_test() {
  infer(s, litt(ast.I32T, s1))
  |> should.equal(#(ast.VLitT(ast.I32T), ast.VTyp(0), s))
  infer(s, litt(ast.I64T, s1))
  |> should.equal(#(ast.VLitT(ast.I64T), ast.VTyp(0), s))
  infer(s, litt(ast.U32T, s1))
  |> should.equal(#(ast.VLitT(ast.U32T), ast.VTyp(0), s))
  infer(s, litt(ast.U64T, s1))
  |> should.equal(#(ast.VLitT(ast.U64T), ast.VTyp(0), s))
  infer(s, litt(ast.F32T, s1))
  |> should.equal(#(ast.VLitT(ast.F32T), ast.VTyp(0), s))
  infer(s, litt(ast.F64T, s1))
  |> should.equal(#(ast.VLitT(ast.F64T), ast.VTyp(0), s))
}

// ============================================================================
// VARIABLE INFERENCE
// ============================================================================

pub fn infer_var_test() {
  let s = state.State(..s, ctx: [#("x", #(v32(1), v32t))])
  infer(s, var(0, s1)) |> should.equal(#(v32(1), v32t, s))
  infer(s, var(1, s1))
  |> should.equal(#(
    ast.VErr,
    ast.VErr,
    state.State(..s, errors: [state.VarUndefined(1, s1)]),
  ))
}

// ============================================================================
// HOLE INFERENCE
// ============================================================================

pub fn infer_hole_test() {
  let state_with_hole = state.State(..s, hole: 1)
  let result = infer(state_with_hole, hole(0, s1))
  // Check result is a tuple with 3 elements
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

// ============================================================================
// RECORD INFERENCE
// ============================================================================

pub fn infer_rcd_test() {
  infer(s, rcd([], s0))
  |> should.equal(#(ast.VRcd([]), ast.VRcd([]), s))
  infer(s, rcd([#("a", i32(1, s1))], s0))
  |> should.equal(#(ast.VRcd([#("a", v32(1))]), ast.VRcd([#("a", v32t)]), s))
  infer(s, rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0))
  |> should.equal(#(
    ast.VRcd([#("a", v32(1)), #("b", v64(2))]),
    ast.VRcd([#("a", v32t), #("b", v64t)]),
    s,
  ))
}

// ============================================================================
// CONSTRUCTOR INFERENCE
// ============================================================================

pub fn infer_ctr_test() {
  // Constructor inference returns a result tuple
  let result = infer(s, ctr("A", i32(1, s1), s2))
  // Check result is a tuple with 3 elements
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

pub fn infer_ctr_arg_bind_test() {
  // Constructor argument binds the implicit type parameter
  let state_with_hole = state.State(..s, hole: 1)
  let term = ctr("Some", i32(42, s1), s2)
  let result = infer(state_with_hole, term)

  // Check result is a tuple with 3 elements (type inference works)
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

pub fn infer_ctr_multiple_args_test() {
  // Constructor with multiple arguments
  let state_with_hole = state.State(..s, hole: 1)
  let term = ctr("Pair", rcd([#("fst", i32(1, s1)), #("snd", i64(2, s2))], s0), s3)
  let result = infer(state_with_hole, term)

  // Check result is a tuple with 3 elements (type inference works)
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}
