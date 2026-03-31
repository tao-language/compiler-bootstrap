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
import core/core as c
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

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
  let id = c.Lam([], #("x", c.Hole(-1, s1)), c.Var(0, s1), s1)
  c.normalize(c.ffi_build, [], id, s1)
  |> should.equal(c.Lam([], #("x", c.Var(-1, s1)), c.Var(0, s1), s1))
}

pub fn normalize_app_test() {
  // Normalize (λx. x) y → y
  let id = c.Lam([], #("x", c.Hole(-1, s1)), c.Var(0, s1), s1)
  let arg = c.LitT(c.I32T, s1)
  let app = c.App(id, [], arg, s1)
  c.normalize(c.ffi_build, [], app, s1)
  |> should.equal(c.LitT(c.I32T, s1))
}

pub fn normalize_nested_app_test() {
  // Normalize (λx. λy. x) a b → a
  let lam_inner = c.Lam([], #("y", c.Hole(-1, s1)), c.Var(1, s1), s1)
  let lam1 = c.Lam([], #("x", c.Hole(-1, s1)), lam_inner, s1)
  let app1 = c.App(lam1, [], c.LitT(c.I32T, s1), s1)
  let app2 = c.App(app1, [], c.LitT(c.I64T, s1), s1)
  c.normalize(c.ffi_build, [], app2, s1)
  |> should.equal(c.LitT(c.I32T, s1))
}

// ============================================================================
// RECORD NORMALIZATION
// ============================================================================

pub fn normalize_dot_test() {
  // Normalize {a = 1}.a → 1
  let rcd = c.Rcd([#("a", c.Lit(c.I32(1), s1))], s1)
  let dot = c.Dot(rcd, "a", s1)
  c.normalize(c.ffi_build, [], dot, s1)
  |> should.equal(c.Lit(c.I32(1), s1))
}

// ============================================================================
// ANNOTATION NORMALIZATION
// ============================================================================

pub fn normalize_ann_test() {
  // Normalize (1 : I32) → 1
  let ann = c.Ann(c.Lit(c.I32(1), s1), c.LitT(c.I32T, s1), s1)
  c.normalize(c.ffi_build, [], ann, s1)
  |> should.equal(c.Lit(c.I32(1), s1))
}
