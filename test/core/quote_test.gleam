// ============================================================================
// QUOTING TESTS
// ============================================================================
/// Tests for quoting values back to syntax.
///
/// Quoting converts semantic values (with De Bruijn levels) back to
/// syntax terms (with De Bruijn indices). This is used for:
/// - Displaying inferred types
/// - Normalization by evaluation
/// - Error message generation
import core/ast as ast
import core/state as state
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

const s = state.initial_state
import core/quote.{quote}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s1 = Span("quote_test", 1, 1, 1, 1)

fn v32(v) {
  ast.VLit(ast.I32(v))
}

fn v64(v) {
  ast.VLit(ast.I64(v))
}

const v32t = ast.VLitT(ast.I32T)

const v64t = ast.VLitT(ast.I64T)

// ============================================================================
// BASIC TYPE QUOTING
// ============================================================================

pub fn quote_typ_test() {
  quote(state.initial_ffis(), 0, ast.VTyp(0), s1)
  |> should.equal(ast.Typ(0, s1))
  quote(state.initial_ffis(), 0, ast.VTyp(1), s1)
  |> should.equal(ast.Typ(1, s1))
}

pub fn quote_lit_test() {
  quote(state.initial_ffis(), 0, v32(1), s1)
  |> should.equal(ast.Lit(ast.I32(1), s1))
  quote(state.initial_ffis(), 0, v64(2), s1)
  |> should.equal(ast.Lit(ast.I64(2), s1))
}

pub fn quote_litt_test() {
  quote(state.initial_ffis(), 0, v32t, s1)
  |> should.equal(ast.LitT(ast.I32T, s1))
  quote(state.initial_ffis(), 0, v64t, s1)
  |> should.equal(ast.LitT(ast.I64T, s1))
}

// ============================================================================
// VARIABLE AND HOLE QUOTING
// ============================================================================

pub fn quote_var_test() {
  // At level 1, HVar(0) should become Var(0)
  quote(state.initial_ffis(), 1, ast.VNeut(ast.HVar(0), []), s1)
  |> should.equal(ast.Var(0, s1))

  // At level 2, HVar(0) should become Var(1)
  quote(state.initial_ffis(), 2, ast.VNeut(ast.HVar(0), []), s1)
  |> should.equal(ast.Var(1, s1))

  // At level 2, HVar(1) should become Var(0)
  quote(state.initial_ffis(), 2, ast.VNeut(ast.HVar(1), []), s1)
  |> should.equal(ast.Var(0, s1))
}

pub fn quote_hole_test() {
  quote(state.initial_ffis(), 0, ast.VNeut(ast.HHole(0), []), s1)
  |> should.equal(ast.Hole(0, s1))
  quote(state.initial_ffis(), 0, ast.VNeut(ast.HHole(5), []), s1)
  |> should.equal(ast.Hole(5, s1))
}

// ============================================================================
// NEUTRAL TERM QUOTING
// ============================================================================

pub fn quote_neut_dot_test() {
  let v = ast.VNeut(ast.HVar(0), [ast.EDot("x")])
  quote(state.initial_ffis(), 1, v, s1)
  |> should.equal(ast.Dot(ast.Var(0, s1), "x", s1))
}

pub fn quote_neut_app_test() {
  let v = ast.VNeut(ast.HVar(0), [ast.EApp(v32t)])
  quote(state.initial_ffis(), 1, v, s1)
  |> should.equal(ast.App(ast.Var(0, s1), [], ast.LitT(ast.I32T, s1), s1))
}

// ============================================================================
// COMPOSITE TYPE QUOTING
// ============================================================================

pub fn quote_rcd_test() {
  let v = ast.VRcd([#("a", v32t), #("b", v64t)])
  quote(state.initial_ffis(), 0, v, s1)
  |> should.equal(ast.Rcd(
    [
      #("a", ast.LitT(ast.I32T, s1)),
      #("b", ast.LitT(ast.I64T, s1)),
    ],
    s1,
  ))
}

pub fn quote_ctr_test() {
  let v = ast.VCtrValue(ast.VCtr("A", v32t))
  quote(state.initial_ffis(), 0, v, s1)
  |> should.equal(ast.Ctr("A", ast.LitT(ast.I32T, s1), s1))
}

pub fn quote_lam_test() {
  // Quoting a lambda creates a fresh variable and quotes the body
  // The parameter type is quoted from VNeut(HVar(lvl), []) which gives Var(-1)
  let v = ast.VLam([], "x", [], ast.Var(0, s1))
  quote(state.initial_ffis(), 0, v, s1)
  |> should.equal(ast.Lam([], #("x", ast.Var(-1, s1)), ast.Var(0, s1), s1))
}

pub fn quote_pi_test() {
  let v = ast.VPi([], "x", [], v32t, ast.Var(0, s1))
  quote(state.initial_ffis(), 0, v, s1)
  |> should.equal(ast.Pi([], "x", ast.LitT(ast.I32T, s1), ast.Var(0, s1), s1))
}

// ============================================================================
// ERROR TYPE QUOTING
// ============================================================================

pub fn quote_verr_test() {
  quote(state.initial_ffis(), 0, ast.VErr, s1)
  |> should.equal(ast.Hole(-1, s1))
}
