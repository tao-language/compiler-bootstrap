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

fn i32(n, s) {
  ast.Lit(ast.I32(n), s)
}

fn lam(name, body, s) {
  ast.Lam([], #(name, ast.Hole(-1, s)), body, s)
}

fn app(fun, arg, s) {
  ast.App(fun, [], arg, s)
}

// ============================================================================
// TYPE EVALUATION
// ============================================================================

pub fn eval_typ_test() {
  eval([], [], typ(0, s1)) |> should.equal(ast.VTyp(0))
  eval([], [], typ(1, s1)) |> should.equal(ast.VTyp(1))
}

// ============================================================================
// LITERAL EVALUATION
// ============================================================================

pub fn eval_lit_test() {
  eval([], [], lit(ast.I32(1), s1))
  |> should.equal(ast.VLit(ast.I32(1)))
  eval([], [], lit(ast.I64(1), s1))
  |> should.equal(ast.VLit(ast.I64(1)))
  eval([], [], lit(ast.U32(1), s1))
  |> should.equal(ast.VLit(ast.U32(1)))
  eval([], [], lit(ast.U64(1), s1))
  |> should.equal(ast.VLit(ast.U64(1)))
  eval([], [], lit(ast.F32(1.0), s1))
  |> should.equal(ast.VLit(ast.F32(1.0)))
  eval([], [], lit(ast.F64(1.0), s1))
  |> should.equal(ast.VLit(ast.F64(1.0)))
}

// ============================================================================
// LITERAL TYPE EVALUATION
// ============================================================================

pub fn eval_litt_test() {
  eval([], [], litt(ast.I32T, s1))
  |> should.equal(ast.VLitT(ast.I32T))
  eval([], [], litt(ast.I64T, s1))
  |> should.equal(ast.VLitT(ast.I64T))
  eval([], [], litt(ast.U32T, s1))
  |> should.equal(ast.VLitT(ast.U32T))
  eval([], [], litt(ast.U64T, s1))
  |> should.equal(ast.VLitT(ast.U64T))
  eval([], [], litt(ast.F32T, s1))
  |> should.equal(ast.VLitT(ast.F32T))
  eval([], [], litt(ast.F64T, s1))
  |> should.equal(ast.VLitT(ast.F64T))
}

// ============================================================================
// VARIABLE EVALUATION
// ============================================================================

pub fn eval_var_test() {
  let env = [v32(0)]
  eval([], env, var(0, s1)) |> should.equal(v32(0))
  eval([], env, var(1, s1)) |> should.equal(ast.VErr)
}

// ============================================================================
// HOLE EVALUATION
// ============================================================================

pub fn eval_hole_test() {
  eval([], [], hole(0, s1)) |> should.equal(vhole(0))
  eval([], [], hole(1, s1)) |> should.equal(vhole(1))
}

// ============================================================================
// LAMBDA BETA-REDUCTION TESTS
// ============================================================================

pub fn eval_lambda_identity_test() {
  // (λx. x) 42 should evaluate to 42
  let identity = lam("x", var(0, s1), s1)  // λx. x
  let arg = i32(42, s1)
  let app_term = app(identity, arg, s1)
  eval([], [], app_term) |> should.equal(v32(42))
}

pub fn eval_lambda_const_test() {
  // (λx. λy. x) 1 2 should evaluate to 1 (K combinator)
  let inner_lam = lam("y", var(1, s1), s1)  // λy. x (x is at index 1)
  let outer_lam = lam("x", inner_lam, s1)   // λx. λy. x
  let arg1 = i32(1, s1)
  let arg2 = i32(2, s1)
  let app1 = app(outer_lam, arg1, s1)
  let app2 = app(app1, arg2, s1)
  eval([], [], app2) |> should.equal(v32(1))
}

pub fn eval_lambda_application_test() {
  // (λf. f 5) (λx. x + 1) - simplified version
  // (λx. x) (λy. y) 42 should evaluate to 42
  let identity_inner = lam("y", var(0, s1), s1)
  let identity_outer = lam("x", identity_inner, s1)
  let arg = i32(42, s1)
  let app_term = app(app(identity_outer, identity_outer, s1), arg, s1)
  eval([], [], app_term) |> should.equal(v32(42))
}
