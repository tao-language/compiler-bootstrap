// ============================================================================
// NORMALIZATION TESTS
// ============================================================================
/// Tests for normalization by evaluation.
///
/// Normalization reduces terms to their normal form by:
/// 1. Evaluating to a value
/// 2. Quoting back to syntax
///
/// This is used for type equality checking and term reduction.
import core/ast as ast
import core/state as state
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

const s = state.initial_state
import core/quote.{normalize}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s1 = Span("normalize_test", 1, 1, 1, 1)

// ============================================================================
// FUNCTION NORMALIZATION
// ============================================================================

pub fn normalize_id_test() {
  // Normalize the identity function
  // The parameter type is quoted from VNeut(HVar(lvl), []) which gives Var(-1)
  let id = ast.Lam([], #("x", ast.Hole(-1, s1)), ast.Var(0, s1), s1)
  normalize(state.initial_ffis(), [], id, s1)
  |> should.equal(ast.Lam([], #("x", ast.Var(-1, s1)), ast.Var(0, s1), s1))
}

pub fn normalize_app_test() {
  // Normalize (λx. x) y → y
  let id = ast.Lam([], #("x", ast.Hole(-1, s1)), ast.Var(0, s1), s1)
  let arg = ast.LitT(ast.I32T, s1)
  let app = ast.App(id, [], arg, s1)
  normalize(state.initial_ffis(), [], app, s1)
  |> should.equal(ast.LitT(ast.I32T, s1))
}

pub fn normalize_nested_app_test() {
  // Normalize (λx. λy. x) a b → a
  let lam_inner = ast.Lam([], #("y", ast.Hole(-1, s1)), ast.Var(1, s1), s1)
  let lam1 = ast.Lam([], #("x", ast.Hole(-1, s1)), lam_inner, s1)
  let app1 = ast.App(lam1, [], ast.LitT(ast.I32T, s1), s1)
  let app2 = ast.App(app1, [], ast.LitT(ast.I64T, s1), s1)
  normalize(state.initial_ffis(), [], app2, s1)
  |> should.equal(ast.LitT(ast.I32T, s1))
}

// ============================================================================
// RECORD NORMALIZATION
// ============================================================================

pub fn normalize_dot_test() {
  // Normalize {a = 1}.a → 1
  let rcd = ast.Rcd([#("a", ast.Lit(ast.I32(1), s1))], s1)
  let dot = ast.Dot(rcd, "a", s1)
  normalize(state.initial_ffis(), [], dot, s1)
  |> should.equal(ast.Lit(ast.I32(1), s1))
}

// ============================================================================
// ANNOTATION NORMALIZATION
// ============================================================================

pub fn normalize_ann_test() {
  // Normalize (1 : I32) → 1
  let ann = ast.Ann(ast.Lit(ast.I32(1), s1), ast.LitT(ast.I32T, s1), s1)
  normalize(state.initial_ffis(), [], ann, s1)
  |> should.equal(ast.Lit(ast.I32(1), s1))
}
