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

// ============================================================================
// Danger zone pinned by the factorial bug: a neutral variable whose level
// is not representable in the quoting environment produces a *negative*
// de Bruijn index instead of failing.
//
// This is what `factorial(n)` hit for n >= 1: the overloaded `*` operator
// value `for(__type). lam(__args) => match __type {...}` beta-reduces with
// the argument record `{n, f(n-1)}`; the dispatch match gets stuck on the
// (neutral) `__type` hole and captures a 2-entry env `[record, hole]`. The
// record's fields contain neutral variables from the caller's 6-entry env
// (`n` at level 5, `f` at level 2). Quoting those neutrals relative to the
// 2-entry captured env yields negative indices: 2 - 5 - 1 = -4 (for n) and
// 2 - 2 - 1 = -1 (for f).
//
// `quote` itself does not validate the frame; the pipeline avoids this by
// always quoting in a level-valid frame: `quote_case` evaluates case bodies
// in the captured *term* frame but quotes the result against the
// placement env (see `placeholder_env` in `quote.gleam`), and `at` now
// rejects the resulting negative indices instead of binding them to the
// head of the env.
// ============================================================================

pub fn quote_vneut_nvar_level_beyond_env_negative_index_test() {
  // A neutral at level 5 quoted in an env of size 2: index = 2 - 5 - 1 = -4
  let q = fn(size, value) { quote([], v.env_push([], size), value) }
  assert q(2, v.var(5)) == tm.Var(-4)
  // A neutral at level 2 quoted in an env of size 2: index = 2 - 2 - 1 = -1
  assert q(2, v.var(2)) == tm.Var(-1)
  // The bound: level must be < env size for a non-negative index
  assert q(3, v.var(2)) == tm.Var(0)
  assert q(6, v.var(5)) == tm.Var(0)
}

pub fn quote_neutral_carrying_foreign_level_negative_index_test() {
  // Mirrors the factorial pipeline: a record value whose field `n` is a
  // neutral at level 5 (created in a 6-entry env) is trapped inside a
  // neutral application; the neutral is then quoted relative to the 2-entry
  // env the dispatch NMatch captured. The record field quotes to Var(-4).
  let record = v.rcd([#("", v.var(5))])
  let neut = v.NApp(v.NVar(1), record)
  let term = quote([], v.env_push([], 2), v.Neut(neut))
  case term {
    tm.App(_, arg) -> {
      let assert tm.Rcd([#("", #(field, _))], _) = arg
      let assert tm.Var(-4) = field
    }
    _ -> panic as "expected app"
  }
}
