/// Tests for the `quote` module — converting Values back to Terms.
///
/// These tests verify:
/// - Basic value constructors (VTyp, VLit, VLitT, VCtr, VRcd, VRcdT)
/// - Neutral term (HVar) quoting with correct binder depth adjustment
/// - VTypeDef quoting
/// - Level→index conversion correctness
import core/literals as lit
import core/quote.{quote}
import core/term as tm
import core/value as v
import gleam/option.{None, Some}

// ============================================================================
// Basic value constructors
// ============================================================================

pub fn quote_vtyp_test() {
  let value = v.Typ(0)
  let term = quote([], [], value)
  assert term == tm.Typ(0)
}

pub fn quote_vlit_test() {
  let value = v.Lit(lit.Int(42))
  let term = quote([], [], value)
  assert term == tm.Lit(lit.Int(42))
}

pub fn quote_vlitt_test() {
  let value = v.LitT(lit.IntT)
  let term = quote([], [], value)
  assert term == tm.LitT(lit.IntT)
}

pub fn quote_vctr_test() {
  let value = v.Ctr("A", v.int(42))
  let term = quote([], [], value)
  assert term == tm.Ctr("A", tm.Lit(lit.Int(42)))
}

pub fn quote_vrcd_test() {
  let value = v.rcd_open([#("x", v.int_t), #("y", v.float_t)], None)
  let term = quote([], [], value)
  assert term
    == tm.rcd_open(
      [#("x", tm.LitT(lit.IntT)), #("y", tm.LitT(lit.FloatT))],
      None,
    )
}

// ============================================================================
// Neutral term quoting — tests DeBruijn index adjustment logic
// ============================================================================

pub fn quote_vneut_nvar_test() {
  // DeBruijn adjustment: index = len(env) - level - 1
  let q = fn(size, value) { quote([], v.env_push([], size), value) }
  assert q(1, v.var(0)) == tm.Var(0)
  assert q(2, v.var(0)) == tm.Var(1)
  assert q(3, v.var(0)) == tm.Var(2)
  assert q(2, v.var(1)) == tm.Var(0)
  assert q(3, v.var(1)) == tm.Var(1)
  assert q(4, v.var(1)) == tm.Var(2)
  assert q(3, v.var(2)) == tm.Var(0)
  assert q(4, v.var(2)) == tm.Var(1)
  assert q(5, v.var(2)) == tm.Var(2)
}

pub fn quote_vneut_nhole_test() {
  let value = v.hole_open([], Some(42))
  let term = quote([], [], value)
  assert term == tm.Hole(Some(42))
}
