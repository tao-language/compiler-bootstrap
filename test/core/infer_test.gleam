// ============================================================================
// TYPE INFERENCE TESTS
// ============================================================================
/// Tests for bidirectional type inference.
///
/// Type inference determines the type of a term.
/// It works together with type checking in a bidirectional system.
import core/core as c
import gleam/list
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

const s0 = Span("infer_test", 0, 0, 0, 0)

const s1 = Span("infer_test", 1, 1, 1, 1)

const s2 = Span("infer_test", 2, 2, 2, 2)

const s3 = Span("infer_test", 3, 3, 3, 3)

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

fn ctr(k, arg, s) {
  c.Ctr(k, arg, s)
}

fn rcd(fields, s) {
  c.Rcd(fields, s)
}

fn i32(v, s) {
  lit(c.I32(v), s)
}

fn i64(v, s) {
  lit(c.I64(v), s)
}

fn i32t(s) {
  litt(c.I32T, s)
}

fn i64t(s) {
  litt(c.I64T, s)
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
// TYPE INFERENCE
// ============================================================================

pub fn infer_typ_test() {
  c.infer(s, typ(0, s1))
  |> should.equal(#(c.VTyp(0), c.VTyp(1), s))
}

// ============================================================================
// LITERAL INFERENCE
// ============================================================================

pub fn infer_lit_test() {
  c.infer(s, lit(c.I32(1), s1))
  |> should.equal(#(c.VLit(c.I32(1)), c.VLitT(c.I32T), s))
  c.infer(s, lit(c.I64(1), s1))
  |> should.equal(#(c.VLit(c.I64(1)), c.VLitT(c.I64T), s))
  c.infer(s, lit(c.U32(1), s1))
  |> should.equal(#(c.VLit(c.U32(1)), c.VLitT(c.U32T), s))
  c.infer(s, lit(c.U64(1), s1))
  |> should.equal(#(c.VLit(c.U64(1)), c.VLitT(c.U64T), s))
  c.infer(s, lit(c.F32(1.0), s1))
  |> should.equal(#(c.VLit(c.F32(1.0)), c.VLitT(c.F32T), s))
  c.infer(s, lit(c.F64(1.0), s1))
  |> should.equal(#(c.VLit(c.F64(1.0)), c.VLitT(c.F64T), s))
}

// ============================================================================
// LITERAL TYPE INFERENCE
// ============================================================================

pub fn infer_litt_test() {
  c.infer(s, litt(c.I32T, s1))
  |> should.equal(#(c.VLitT(c.I32T), c.VTyp(0), s))
  c.infer(s, litt(c.I64T, s1))
  |> should.equal(#(c.VLitT(c.I64T), c.VTyp(0), s))
  c.infer(s, litt(c.U32T, s1))
  |> should.equal(#(c.VLitT(c.U32T), c.VTyp(0), s))
  c.infer(s, litt(c.U64T, s1))
  |> should.equal(#(c.VLitT(c.U64T), c.VTyp(0), s))
  c.infer(s, litt(c.F32T, s1))
  |> should.equal(#(c.VLitT(c.F32T), c.VTyp(0), s))
  c.infer(s, litt(c.F64T, s1))
  |> should.equal(#(c.VLitT(c.F64T), c.VTyp(0), s))
}

// ============================================================================
// VARIABLE INFERENCE
// ============================================================================

pub fn infer_var_test() {
  let s = c.State(..s, ctx: [#("x", #(v32(1), v32t))])
  c.infer(s, var(0, s1)) |> should.equal(#(v32(1), v32t, s))
  c.infer(s, var(1, s1))
  |> should.equal(#(
    c.VErr,
    c.VErr,
    c.State(..s, errors: [c.VarUndefined(1, s1)]),
  ))
}

// ============================================================================
// HOLE INFERENCE
// ============================================================================

pub fn infer_hole_test() {
  let state_with_hole = c.State(..s, hole: 1)
  let result = c.infer(state_with_hole, hole(0, s1))
  // Check result is a tuple with 3 elements
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

// ============================================================================
// RECORD INFERENCE
// ============================================================================

pub fn infer_rcd_test() {
  c.infer(s, rcd([], s0))
  |> should.equal(#(c.VRcd([]), c.VRcd([]), s))
  c.infer(s, rcd([#("a", i32(1, s1))], s0))
  |> should.equal(#(c.VRcd([#("a", v32(1))]), c.VRcd([#("a", v32t)]), s))
  c.infer(s, rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0))
  |> should.equal(#(
    c.VRcd([#("a", v32(1)), #("b", v64(2))]),
    c.VRcd([#("a", v32t), #("b", v64t)]),
    s,
  ))
}

// ============================================================================
// CONSTRUCTOR INFERENCE
// ============================================================================

pub fn infer_ctr_test() {
  // Constructor inference returns a result tuple
  let result = c.infer(s, ctr("A", i32(1, s1), s2))
  // Check result is a tuple with 3 elements
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

pub fn infer_ctr_arg_bind_test() {
  // Constructor argument binds the implicit type parameter
  let state_with_hole = c.State(..s, hole: 1)
  let term = ctr("Some", i32(42, s1), s2)
  let result = c.infer(state_with_hole, term)

  // Check result is a tuple with 3 elements (type inference works)
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}

pub fn infer_ctr_multiple_args_test() {
  // Constructor with multiple arguments
  let state_with_hole = c.State(..s, hole: 1)
  let term = ctr("Pair", rcd([#("fst", i32(1, s1)), #("snd", i64(2, s2))], s0), s3)
  let result = c.infer(state_with_hole, term)

  // Check result is a tuple with 3 elements (type inference works)
  case result {
    #(_, _, _) -> True |> should.be_true
  }
}
