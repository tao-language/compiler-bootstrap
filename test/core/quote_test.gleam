/// Tests for the `quote` module — converting Values back to Terms.
///
/// These tests verify:
/// - Basic value constructors (VTyp, VLit, VLitT, VCtr, VRcd, VRcdT)
/// - Neutral terms (HVar, HHole, HCall)
/// - Eliminators (EApp, EFix, EMatch)
/// - Lambda and Pi quoting with correct binder depth
/// - VTypeDef quoting
/// - Level→index conversion correctness
import core/ast
import core/quote.{quote}
import core/state.{State, new_state, with_err}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("quote_test", 0, 0, 0, 0)

const s1 = Span("quote_test", 1, 1, 1, 1)

const s2 = Span("quote_test", 2, 2, 2, 2)

const s3 = Span("quote_test", 3, 3, 3, 3)

// ============================================================================
// Existing tests (unchanged)
// ============================================================================

pub fn quote_vtyp_test() {
  let value = ast.VTyp(0)
  let term = quote([], value, s)
  assert term == ast.Typ(0, s)
}

pub fn quote_vlit_test() {
  let value = ast.VLit(ast.Int(42))
  let term = quote([], value, s)
  assert term == ast.Lit(ast.Int(42), s)
}

pub fn quote_vlitt_test() {
  let value = ast.VLitT(ast.IntT)
  let term = quote([], value, s)
  assert term == ast.LitT(ast.IntT, s)
}

pub fn quote_vctr_test() {
  let value = ast.VCtr("A", ast.vint(42))
  let term = quote([], value, s)
  assert term == ast.Ctr("A", ast.int(42, s), s)
}

pub fn quote_vrcd_test() {
  let value = ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
  let term = quote([], value, s)
  assert term == ast.Rcd([#("x", ast.int_t(s)), #("y", ast.float_t(s))], s)
}

pub fn quote_vrcdt_test() {
  let value =
    ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
  let term = quote([], value, s)
  assert term
    == ast.RcdT(
      [#("x", ast.int_t(s), Some(ast.int(42, s))), #("y", ast.float_t(s), None)],
      s,
    )
}

pub fn quote_vneut_hvar_test() {
  // De Bruijn levels map directly to De Bruijn indices:
  // level 0 = innermost binder = index 0
  // level 1 = next binder = index 1
  assert quote([], ast.vvar(0, []), s) == ast.Var(0, s)
  assert quote([], ast.vvar(1, []), s) == ast.Var(1, s)
  assert quote([], ast.vvar(2, []), s) == ast.Var(2, s)
}

pub fn quote_vneut_hhole_test() {
  let value = ast.VNeut(ast.HHole(42), [])
  let term = quote([], value, s)
  assert term == ast.Hole(42, s)
}
