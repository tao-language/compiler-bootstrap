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

const s1 = Span("quote_test", 1, 1, 1, 1)

fn v32(v) {
  c.VLit(c.I32(v))
}

fn v64(v) {
  c.VLit(c.I64(v))
}

const v32t = c.VLitT(c.I32T)

const v64t = c.VLitT(c.I64T)

// ============================================================================
// BASIC TYPE QUOTING
// ============================================================================

pub fn quote_typ_test() {
  c.quote(c.ffi_build, 0, c.VTyp(0), s1)
  |> should.equal(c.Typ(0, s1))
  c.quote(c.ffi_build, 0, c.VTyp(1), s1)
  |> should.equal(c.Typ(1, s1))
}

pub fn quote_lit_test() {
  c.quote(c.ffi_build, 0, v32(1), s1)
  |> should.equal(c.Lit(c.I32(1), s1))
  c.quote(c.ffi_build, 0, v64(2), s1)
  |> should.equal(c.Lit(c.I64(2), s1))
}

pub fn quote_litt_test() {
  c.quote(c.ffi_build, 0, v32t, s1)
  |> should.equal(c.LitT(c.I32T, s1))
  c.quote(c.ffi_build, 0, v64t, s1)
  |> should.equal(c.LitT(c.I64T, s1))
}

// ============================================================================
// VARIABLE AND HOLE QUOTING
// ============================================================================

pub fn quote_var_test() {
  // At level 1, HVar(0) should become Var(0)
  c.quote(c.ffi_build, 1, c.VNeut(c.HVar(0), []), s1)
  |> should.equal(c.Var(0, s1))

  // At level 2, HVar(0) should become Var(1)
  c.quote(c.ffi_build, 2, c.VNeut(c.HVar(0), []), s1)
  |> should.equal(c.Var(1, s1))

  // At level 2, HVar(1) should become Var(0)
  c.quote(c.ffi_build, 2, c.VNeut(c.HVar(1), []), s1)
  |> should.equal(c.Var(0, s1))
}

pub fn quote_hole_test() {
  c.quote(c.ffi_build, 0, c.VNeut(c.HHole(0), []), s1)
  |> should.equal(c.Hole(0, s1))
  c.quote(c.ffi_build, 0, c.VNeut(c.HHole(5), []), s1)
  |> should.equal(c.Hole(5, s1))
}

// ============================================================================
// NEUTRAL TERM QUOTING
// ============================================================================

pub fn quote_neut_dot_test() {
  let v = c.VNeut(c.HVar(0), [c.EDot("x")])
  c.quote(c.ffi_build, 1, v, s1)
  |> should.equal(c.Dot(c.Var(0, s1), "x", s1))
}

pub fn quote_neut_app_test() {
  let v = c.VNeut(c.HVar(0), [c.EApp(v32t)])
  c.quote(c.ffi_build, 1, v, s1)
  |> should.equal(c.App(c.Var(0, s1), [], c.LitT(c.I32T, s1), s1))
}

// ============================================================================
// COMPOSITE TYPE QUOTING
// ============================================================================

pub fn quote_rcd_test() {
  let v = c.VRcd([#("a", v32t), #("b", v64t)])
  c.quote(c.ffi_build, 0, v, s1)
  |> should.equal(c.Rcd(
    [
      #("a", c.LitT(c.I32T, s1)),
      #("b", c.LitT(c.I64T, s1)),
    ],
    s1,
  ))
}

pub fn quote_ctr_test() {
  let v = c.VCtrValue(c.VCtr("A", v32t))
  c.quote(c.ffi_build, 0, v, s1)
  |> should.equal(c.Ctr("A", c.LitT(c.I32T, s1), s1))
}

pub fn quote_lam_test() {
  // Quoting a lambda creates a fresh variable and quotes the body
  // The parameter type is quoted from VNeut(HVar(lvl), []) which gives Var(-1)
  let v = c.VLam([], "x", [], c.Var(0, s1))
  c.quote(c.ffi_build, 0, v, s1)
  |> should.equal(c.Lam([], #("x", c.Var(-1, s1)), c.Var(0, s1), s1))
}

pub fn quote_pi_test() {
  let v = c.VPi([], "x", [], v32t, c.Var(0, s1))
  c.quote(c.ffi_build, 0, v, s1)
  |> should.equal(c.Pi([], "x", c.LitT(c.I32T, s1), c.Var(0, s1), s1))
}

// ============================================================================
// ERROR TYPE QUOTING
// ============================================================================

pub fn quote_verr_test() {
  c.quote(c.ffi_build, 0, c.VErr, s1)
  |> should.equal(c.Hole(-1, s1))
}
