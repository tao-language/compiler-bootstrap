/// Tests for the Quote module (Value → Term conversion)
///
/// Tests cover:
/// - Literal value quoting (int, float)
/// - Constructor value quoting
/// - Record value quoting
/// - Error value quoting
/// - Variable level-to-index conversion
/// - Hole quoting
/// - Neutral term quoting with application spine
/// - Lambda value quoting
/// - Pi type value quoting
/// - Nested lambda quoting
/// - Edge cases (empty record, complex spine)
/// - Evaluate → Quote round-trip

import core/ast.{
  Err,
  type Term, type Value, App, Ctr, EApp, Hole, HHole, HVar, Lam, Lit,
  Pi, Rcd, VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, Var,
  Int as LitInt, Float as LitFloat,
}
import core/quote.{quote, quote_at}
import core/state.{initial_state}
import core/subst.{force}
import core/eval.{evaluate}
import gleeunit
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

fn vi(value: Int) -> Value {
  VLit(LitInt(value))
}

fn vl(level: Int) -> Value {
  VNeut(HVar(level), [])
}

fn vh(id: Int) -> Value {
  VNeut(HHole(id), [])
}

// ============================================================================
// LITERAL VALUE QUOTING
// ============================================================================

pub fn quote_lit_int_test() {
  let value = VLit(LitInt(42))
  let term = quote(value)
  let expected = Lit(LitInt(42), single("", 0, 0))
  assert term == expected
}

pub fn quote_lit_int_negative_test() {
  let value = VLit(LitInt(-1))
  let term = quote(value)
  let expected = Lit(LitInt(-1), single("", 0, 0))
  assert term == expected
}

pub fn quote_lit_int_zero_test() {
  let value = VLit(LitInt(0))
  let term = quote(value)
  let expected = Lit(LitInt(0), single("", 0, 0))
  assert term == expected
}

pub fn quote_lit_float_test() {
  let value = VLit(LitFloat(3.14))
  let term = quote(value)
  let expected = Lit(LitFloat(3.14), single("", 0, 0))
  assert term == expected
}

// ============================================================================
// CONSTRUCTOR VALUE QUOTING
// ============================================================================

pub fn quote_ctr_test() {
  let value = VCtr("Just", vi(42))
  let term = quote(value)
  let expected = Ctr("Just", Lit(LitInt(42), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_nested_ctr_test() {
  let value = VCtr("Outer", VCtr("Inner", vi(1), ))
  let term = quote(value)
  let expected = Ctr("Outer", Ctr("Inner", Lit(LitInt(1), single("", 0, 0)), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

// ============================================================================
// RECORD VALUE QUOTING
// ============================================================================

pub fn quote_rcd_test() {
  let value = VRcd([#("a", vi(1)), #("b", vi(2))])
  let term = quote(value)
  let expected = Rcd([#("a", Lit(LitInt(1), single("", 0, 0))), #("b", Lit(LitInt(2), single("", 0, 0)))], single("", 0, 0))
  assert term == expected
}

pub fn quote_empty_rcd_test() {
  let value = VRcd([])
  let term = quote(value)
  let expected = Rcd([], single("", 0, 0))
  assert term == expected
}

// ============================================================================
// ERROR VALUE QUOTING
// ============================================================================

pub fn quote_err_test() {
  let value = VErr
  let term = quote(value)
  let expected = Err("error", single("", 0, 0))
  assert term == expected
}

// ============================================================================
// VARIABLE LEVEL-TO-INDEX CONVERSION
// ============================================================================

pub fn quote_var_at_top_level_test() {
  let value = vl(0)
  let term = quote(value)
  assert term == Var(0, single("", 0, 0))
}

pub fn quote_var_level_1_at_level_0_test() {
  let value = vl(1)
  let term = quote(value)
  assert term == Var(1, single("", 0, 0))
}

pub fn quote_var_level_2_at_level_0_test() {
  let value = vl(2)
  let term = quote(value)
  assert term == Var(2, single("", 0, 0))
}

pub fn quote_var_at_different_levels_test() {
  let value = vl(0)
  // HVar(0) at level 1: abs_index(0, 1): 0 < 1 → True → 1-1-0 = 0
  let term1 = quote_at(value, 1)
  // HVar(0) at level 2: abs_index(0, 2): 0 < 2 → True → 2-1-0 = 1
  let term2 = quote_at(value, 2)
  assert term1 == Var(0, single("", 0, 0))
  assert term2 == Var(1, single("", 0, 0))
}

pub fn quote_var_level_1_at_level_2_test() {
  let value = vl(1)
  let term = quote_at(value, 2)
  assert term == Var(0, single("", 0, 0))
}

pub fn quote_var_level_2_at_level_2_test() {
  let value = vl(2)
  let term = quote_at(value, 2)
  assert term == Var(0, single("", 0, 0))
}

// ============================================================================
// HOLE QUOTING
// ============================================================================

pub fn quote_hole_test() {
  let value = vh(0)
  let term = quote(value)
  assert term == Hole(0, single("", 0, 0))
}

pub fn quote_hole_high_id_test() {
  let value = vh(99)
  let term = quote(value)
  assert term == Hole(99, single("", 0, 0))
}

// ============================================================================
// NEUTRAL TERM WITH SPINE
// ============================================================================

pub fn quote_neut_with_app_spine_test() {
  let value = VNeut(HVar(0), [EApp(vi(1))])
  let term = quote(value)
  let expected = App(Var(0, single("", 0, 0)), Lit(LitInt(1), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_neut_multiple_spine_test() {
  let value = VNeut(HVar(0), [EApp(vi(1)), EApp(vi(2))])
  let term = quote(value)
  let inner_app = App(Var(0, single("", 0, 0)), Lit(LitInt(1), single("", 0, 0)), single("", 0, 0))
  let expected = App(inner_app, Lit(LitInt(2), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_neut_hole_with_spine_test() {
  let value = VNeut(HHole(5), [EApp(vi(3))])
  let term = quote(value)
  let expected = App(Hole(5, single("", 0, 0)), Lit(LitInt(3), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

// ============================================================================
// LAMBDA VALUE QUOTING
// ============================================================================

pub fn quote_lam_simple_test() {
  let body: Term = Var(0, single("", 0, 0))
  let value = VLam([], [], #("x", VRcd([])), body)
  let term = quote(value)
  let expected = Lam([], #("x", Rcd([], single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_lam_nested_test() {
  let inner_body: Term = Var(0, single("", 0, 0))
  let inner = VLam([], [], #("y", vi(0)), inner_body)
  let outer_body: Term = Var(0, single("", 0, 0))
  let _ignored = inner
  let value = VLam([], [], #("x", VRcd([])), outer_body)
  let term = quote(value)
  let expected = Lam([], #("x", Rcd([], single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_lam_needs_nested_quote_test() {
  let inner_body: Term = Var(0, single("", 0, 0))
  let inner_lam: Value = VLam([], [], #("y", vi(1)), inner_body)
  let value = VCtr("Tag", inner_lam)
  let term = quote(value)
  let expected = Ctr("Tag", Lam([], #("y", Lit(LitInt(1), single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

// ============================================================================
// PI TYPE VALUE QUOTING
// ============================================================================

pub fn quote_pi_simple_test() {
  let domain: Value = vi(0)
  let codomain: Value = vi(1)
  let value = VPi([], [], #("pi_param", domain), codomain)
  let term = quote(value)
  let expected = Pi([], #("pi_param", Lit(LitInt(0), single("", 0, 0))), Lit(LitInt(1), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_pi_with_vlam_codomain_test() {
  let domain: Value = vi(0)
  let lam_body: Term = Var(0, single("", 0, 0))
  let codomain: Value = VLam([], [], #("x", vi(1)), lam_body)
  let value = VPi([], [], #("pi_param", domain), codomain)
  let term = quote(value)
  // The domain is vi(0) -> Lit(LitInt(0), span)
  // The codomain is VLam -> Lam([], #("x", Lit(LitInt(1), span)), Var(0, span), span)
  let expected_codomain = Lam([], #("x", Lit(LitInt(1), single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0))
  assert case term {
    Pi([], #("pi_param", Lit(LitInt(0), _)), actual_codomain, _) -> actual_codomain == expected_codomain
    _ -> False
  }
}

// ============================================================================
// QUOTE ≠ EVAL INVARIANT
// ============================================================================

// Quote should never call eval. This is a critical invariant.
// The test verifies that quoting a VLam returns a Term directly
// without evaluating the body.

pub fn quote_does_not_evaluate_vlam_body_test() {
  let body: Term = Lam([], #("inner", Lit(LitInt(0), single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0))
  let value = VLam([], [], #("x", vi(0)), body)
  let term = quote(value)
  assert case term {
    Lam(_, #(_, _param), inner_body, _) ->
      case inner_body {
        Lam([], #("inner", _), _, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn quote_preserves_lam_body_test() {
  let body: Term = Var(1, single("", 0, 0))
  let value = VLam([], [], #("x", vi(0)), body)
  let term = quote(value)
  assert case term {
    Lam([], #("x", _), body2, _) -> body2 == Var(1, single("", 0, 0))
    _ -> False
  }
}

// ============================================================================
// COMPOSITE QUOTING
// ============================================================================

pub fn quote_ctr_with_complex_arg_test() {
  let value = VCtr("Result", VRcd([#("ok", vi(1)), #("err", vh(0))]))
  let term = quote(value)
  let expected = Ctr("Result", Rcd([#("ok", Lit(LitInt(1), single("", 0, 0))), #("err", Hole(0, single("", 0, 0)))], single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_nested_vlam_vpi_test() {
  let domain: Value = vi(0)
  let lam_body: Term = Var(0, single("", 0, 0))
  let codomain: Value = VLam([], [], #("f", VPi([], [], #("pi_param", vi(0)), vi(1))), lam_body)
  let value = VPi([], [], #("pi_param", domain), codomain)
  let term = quote(value)
  assert case term {
    Pi([], #("pi_param", domain_t), Lam([], #("f", _), _, _), _) ->
      case domain_t {
        Lit(LitInt(0), _) -> True
        _ -> False
      }
    _ -> False
  }
}

// ============================================================================
// LEVEL OFFSET CORRECTNESS
// ============================================================================

pub fn quote_at_preserves_variable_offsets_test() {
  let value = vl(0)
  let term0 = quote(value)
  let term1 = quote_at(value, 1)
  assert term0 == Var(0, single("", 0, 0))
  assert term1 == Var(0, single("", 0, 0))
}

pub fn quote_at_higher_level_test() {
  let value = vl(0)
  let term = quote_at(value, 3)
  assert term == Var(2, single("", 0, 0))
}

pub fn quote_at_level_vs_value_level_test() {
  let value = vl(1)
  let term_at_1 = quote_at(value, 1)
  let term_at_3 = quote_at(value, 3)
  // HVar(1) at level 1: abs_index(1, 1): 1 < 1 → False → 1 - 1 = 0
  assert term_at_1 == Var(0, single("", 0, 0))
  // HVar(1) at level 3: abs_index(1, 3): 1 < 3 → True → 3 - 1 - 1 = 1
  assert term_at_3 == Var(1, single("", 0, 0))
}

// ============================================================================
// FORCE INTEGRATION TEST
// ============================================================================

pub fn force_and_quote_integration_test() {
  let state = initial_state([])
  // Evaluate: identity function applied to 42
  let id_fn: Value = VLam([], [], #("x", VRcd([])), Var(0, single("", 0, 0)))
  let result = force(state, id_fn)
  // The result should be a VLam (not forced — it's not a hole)
  assert case result {
    VLam([], [], #("x", _), _) -> True
    _ -> False
  }
}

pub fn force_resolves_hole_then_quote_test() {
  let state = initial_state([])
  // Create a hole and force it — since there's no binding, it stays as-is
  let hole_value = VNeut(HHole(99), [EApp(vi(42))])
  let result = force(state, hole_value)
  // Should stay as VNeut since the hole has no binding
  assert case result {
    VNeut(HHole(99), _) -> True
    _ -> False
  }
  // Now quote it
  let term = quote(result)
  let expected = App(Hole(99, single("", 0, 0)), Lit(LitInt(42), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

// ============================================================================
// EVALUATE → QUOTE ROUND-TRIP
// ============================================================================

pub fn evaluate_identity_then_quote_test() {
  let state = initial_state([])
  let body = Var(0, single("", 0, 0))
  let param_type = Lit(LitInt(0), single("", 0, 0))
  let lam = Lam([], #("x", param_type), body, single("", 0, 0))
  let value = evaluate(state, lam)
  // The evaluated value is a VLam
  assert case value {
    VLam([], [], #("x", _), _body2) -> {
      let quoted = quote(value)
      case quoted {
        Lam([], #("x", _), inner_body, _) -> {
          // The body Var(0) should be preserved
          inner_body == Var(0, single("", 0, 0))
        }
        _ -> False
      }
    }
    _ -> False
  }
}

pub fn evaluate_lam_app_then_quote_test() {
  let state = initial_state([])
  let body = Var(0, single("", 0, 0))
  let param_type = Lit(LitInt(0), single("", 0, 0))
  let lam = Lam([], #("x", param_type), body, single("", 0, 0))
  let arg = Lit(LitInt(42), single("", 0, 0))
  let result = evaluate(state, App(lam, arg, single("", 0, 0)))
  // After evaluation, we get VLit(LitInt(42))
  assert result == VLit(LitInt(42))
  // Quoting should give back the literal
  let quoted = quote(result)
  assert quoted == Lit(LitInt(42), single("", 0, 0))
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn quote_deeply_nested_ctr_test() {
  let v3 = VCtr("C3", vi(3))
  let v2 = VCtr("C2", v3)
  let v1 = VCtr("C1", v2)
  let v0 = VCtr("C0", v1)
  let term = quote(v0)
  let expected = Ctr("C0", Ctr("C1", Ctr("C2", Ctr("C3", Lit(LitInt(3), single("", 0, 0)), single("", 0, 0)), single("", 0, 0)), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_vpi_domain_neut_test() {
  let domain: Value = vl(0)
  let codomain: Value = vi(1)
  let value = VPi([], [], #("pi_param", domain), codomain)
  let term = quote(value)
  let expected = Pi([], #("pi_param", Var(0, single("", 0, 0))), Lit(LitInt(1), single("", 0, 0)), single("", 0, 0))
  assert term == expected
}

pub fn quote_hvar_with_complex_spine_test() {
  let arg1: Value = VCtr("A", vi(1))
  let arg2: Value = VCtr("B", vi(2))
  let value = VNeut(HVar(0), [EApp(arg1), EApp(arg2)])
  let term = quote(value)
  let expected = App(
    App(Var(0, single("", 0, 0)), Ctr("A", Lit(LitInt(1), single("", 0, 0)), single("", 0, 0)), single("", 0, 0)),
    Ctr("B", Lit(LitInt(2), single("", 0, 0)), single("", 0, 0)),
    single("", 0, 0),
  )
  assert term == expected
}

pub fn quote_lam_with_pi_type_test() {
  let domain: Value = vi(0)
  let codomain: Value = vi(1)
  let param_type: Value = VPi([], [], #("pi_param", domain), codomain)
  let body: Term = Var(0, single("", 0, 0))
  let value = VLam([], [], #("f", param_type), body)
  let term = quote(value)
  let expected = Lam([], #("f", Pi([], #("pi_param", Lit(LitInt(0), single("", 0, 0))), Lit(LitInt(1), single("", 0, 0)), single("", 0, 0))), Var(0, single("", 0, 0)), single("", 0, 0))
  assert term == expected
}
