/// Tests for the `quote` module — converting Values back to Terms.
///
/// These tests verify:
/// - Basic value constructors (VTyp, VLit, VLitT, VCtr, VRcd, VRcdT)
/// - Neutral terms (HVar, HHole, HCall)
/// - Eliminators (EApp, EFix, EMatch)
/// - Lambda and Pi quoting with correct binder depth
/// - VTypeDef quoting
/// - Level→index conversion correctness
import core/term.{type Term} as tm
import core/literals.{type Literal} as lit
import core/quote.{quote}
import core/value.{type Value} as v
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("quote_test", 0, 0, 0, 0)

// ============================================================================
// Existing tests (unchanged)
// ============================================================================

pub fn quote_vtyp_test() {
  let value = v.Typ(0)
  let term = quote([], 0, value)
  assert term == tm.Typ(0)
}

pub fn quote_vlit_test() {
  let value = v.Lit(lit.Int(42))
  let term = quote([], 0, value)
  assert term == tm.Lit(lit.Int(42))
}

pub fn quote_vlitt_test() {
  let value = v.LitT(lit.IntT)
  let term = quote([], 0, value)
  assert term == tm.LitT(lit.IntT)
}

pub fn quote_vctr_test() {
  let value = v.Ctr("A", v.int(42))
  let term = quote([], 0, value)
  assert term == tm.Ctr("A", tm.int(42))
}

pub fn quote_vrcd_test() {
  let value = v.Rcd([#("x", v.int_t), #("y", v.float_t)])
  let term = quote([], 0, value)
  assert term == tm.Rcd([#("x", tm.int_t), #("y", tm.float_t)])
}

pub fn quote_vrcdt_test() {
  let value =
    v.RcdT([
      #("x", v.int_t, Some(v.int(42))),
      #("y", v.float_t, None),
    ])
  let term = quote([], 0, value)
  assert term
    == tm.RcdT([
      #("x", tm.int_t, Some(tm.int(42))),
      #("y", tm.float_t, None),
    ])

}

pub fn quote_vneut_nvar_test() {
  assert quote([], 1, v.var(0)) == tm.Var(0)
  assert quote([], 2, v.var(0)) == tm.Var(1)
  assert quote([], 3, v.var(0)) == tm.Var(2)
  assert quote([], 2, v.var(1)) == tm.Var(0)
  assert quote([], 3, v.var(1)) == tm.Var(1)
  assert quote([], 4, v.var(1)) == tm.Var(2)
  assert quote([], 3, v.var(2)) == tm.Var(0)
  assert quote([], 4, v.var(2)) == tm.Var(1)
  assert quote([], 5, v.var(2)) == tm.Var(2)
}

pub fn quote_vneut_nhole_test() {
  let value = v.hole(42)
  let term = quote([], 0, value)
  assert term == tm.Hole(42)
}
