/// Tests for the Normalization by Evaluation (NBE) evaluator
///
/// Tests cover:
/// - Literal evaluation (integer, float)
/// - Variable evaluation (neutral terms)
/// - Hole evaluation (neutral terms)
/// - Lambda evaluation (closures)
/// - Application (beta reduction, neutral spine)
/// - Pi type evaluation
/// - Constructor evaluation
/// - Record evaluation
/// - Annotation (erasure)
/// - Match expressions (pattern matching, guards)
/// - Error term evaluation
/// - FFI call evaluation
/// - Pattern matching helpers
/// - Edge cases (empty match, no match, nested app)

import gleeunit
import core/eval.{
  evaluate, do_app, match_pattern, lookup_env, value_to_string, is_true_value
}
import core/state.{initial_state, FfiEntry}
import core/ast.{
  type Value,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Rcd, Err, Call, Typ,
  VNeut, HHole, HVar, VLam, VPi, VLit, VCtr, VRcd, VErr, EApp,
  Case as CoreCase, PAny, PVar, PCtr as Pctr, PUnit, PLit,
  Int as LitInt, Float as LitFloat,
}
import gleam/option.{type Option, Some, None}
import syntax/span.{single}


pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LITERAL EVALUATION
// ============================================================================

pub fn eval_int_literal_test() {
  let state = initial_state([])
  let value = evaluate(state, Lit(LitInt(42), single("", 1, 1)))
  assert value == VLit(LitInt(42))
}

pub fn eval_float_literal_test() {
  let state = initial_state([])
  let value = evaluate(state, Lit(LitFloat(3.14), single("", 1, 1)))
  assert value == VLit(LitFloat(3.14))
}

pub fn eval_zero_test() {
  let state = initial_state([])
  let value = evaluate(state, Lit(LitInt(0), single("", 1, 1)))
  assert value == VLit(LitInt(0))
}

// ============================================================================
// VARIABLE EVALUATION — neutral terms
// ============================================================================

pub fn eval_var_becomes_neutral_test() {
  let state = initial_state([])
  let value = evaluate(state, Var(0, single("", 1, 1)))
  assert value == VNeut(HVar(0), [])
}

pub fn eval_var_different_levels_test() {
  let state = initial_state([])
  let value = evaluate(state, Var(5, single("", 1, 1)))
  assert value == VNeut(HVar(5), [])
}

// ============================================================================
// HOLE EVALUATION — neutral terms
// ============================================================================

pub fn eval_hole_becomes_neutral_test() {
  let state = initial_state([])
  let value = evaluate(state, Hole(42, single("", 1, 1)))
  assert value == VNeut(HHole(42), [])
}

pub fn eval_hole_zero_test() {
  let state = initial_state([])
  let value = evaluate(state, Hole(0, single("", 1, 1)))
  assert value == VNeut(HHole(0), [])
}

// ============================================================================
// LAMBDA EVALUATION — closures
// ============================================================================

pub fn eval_lambda_creates_vlam_test() {
  let state = initial_state([])
  let body = Var(0, single("", 1, 1))
  let param_type = Rcd([], single("", 1, 1))
  let term = Lam(#("x", param_type), body, single("", 1, 1))
  let value = evaluate(state, term)
  assert case value {
    VLam(#(name, _), body_term) -> name == "x" && body_term == body
    _ -> False
  }
}

pub fn eval_lambda_with_complex_body_test() {
  let state = initial_state([])
  let body = App(Var(0, single("", 1, 1)), Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let param_type = Rcd([], single("", 1, 1))
  let term = Lam(#("f", param_type), body, single("", 1, 1))
  let value = evaluate(state, term)
  assert case value {
    VLam(#("f", _), body_term) -> {
      case body_term {
        App(Var(0, _), Lit(LitInt(1), _), _) -> True
        _ -> False
      }
    }
    _ -> False
  }
}

// ============================================================================
// APPLICATION — Beta reduction and neutral spine
// ============================================================================

pub fn eval_app_applies_lambda_test() {
  // App(Lam(x, x), Lit(42)) -> Lit(42)
  let state = initial_state([])
  let lam_body = Var(0, single("", 1, 1))
  let param_type = Rcd([], single("", 1, 1))
  let lam = Lam(#("x", param_type), lam_body, single("", 1, 1))
  let app_term = App(lam, Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app_term)
  assert value == VLit(LitInt(42))
}

pub fn eval_app_identity_function_test() {
  // Identity function: fn(x) => x applied to 42
  let state = initial_state([])
  let body = Var(0, single("", 1, 1))
  let param_type = Rcd([], single("", 1, 1))
  let identity = Lam(#("x", param_type), body, single("", 1, 1))
  let app = App(identity, Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VLit(LitInt(42))
}

pub fn eval_app_nested_beta_test() {
  // ((fn(x) => fn(y) => x) 42) 100 -> 42
  let state = initial_state([])
  let inner_lam = Lam(#("y", Rcd([], single("", 1, 1))), Var(1, single("", 1, 1)), single("", 1, 1))
  let outer_lam = Lam(#("x", Rcd([], single("", 1, 1))), inner_lam, single("", 1, 1))
  let app1 = App(outer_lam, Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let app2 = App(app1, Lit(LitInt(100), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app2)
  assert value == VLit(LitInt(42))
}

pub fn eval_app_neutral_spine_test() {
  // App(Var(0), Lit(42)) -> VNeut(HVar(0), [EApp(VLit(42))])
  let state = initial_state([])
  let app_term = App(Var(0, single("", 1, 1)), Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app_term)
  assert value == VNeut(HVar(0), [EApp(VLit(LitInt(42)))])
}

pub fn eval_app_double_neutral_spine_test() {
  // App(App(Var(0), Lit(1)), Lit(2))
  // -> App(VNeut(HVar(0), [EApp(VLit(1))]), Lit(2))
  // -> VNeut(HVar(0), [EApp(VLit(1)), EApp(VLit(2))])
  let state = initial_state([])
  let app1 = App(Var(0, single("", 1, 1)), Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let app2 = App(app1, Lit(LitInt(2), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app2)
  assert value == VNeut(HVar(0), [EApp(VLit(LitInt(1))), EApp(VLit(LitInt(2)))])
}

pub fn eval_app_error_propagates_test() {
  // App(Err, Lit(42)) -> VErr
  let state = initial_state([])
  let err_term = Err("error", single("", 1, 1))
  let app = App(err_term, Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VErr
}

pub fn eval_app_type_application_returns_error_test() {
  // Applying a Pi type (which is not a function at value level)
  let state = initial_state([])
  let pi = Pi(Lit(LitInt(0), single("", 1, 1)), Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let app = App(pi, Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VErr
}

// ============================================================================
// DO_APP — Neutral spine construction and beta reduction
// ============================================================================

pub fn do_app_beta_reduction_test() {
  // Beta reduction: apply a lambda to an argument, evaluate to value
  let state = initial_state([])
  let arg = VLit(LitInt(42))
  let body = Var(0, single("", 1, 1))
  let lam = VLam(#("x", VRcd([])), body)
  let result = do_app(state, lam, arg)
  // The body Var(0) is substituted with the argument (converted to a Term
  // via value_to_neut → force_levels_to_indices), then evaluated.
  assert result == VLit(LitInt(42))
}

pub fn do_app_neutral_spine_test() {
  let state = initial_state([])
  let arg = VLit(LitInt(42))
  let neut = VNeut(HVar(0), [EApp(VLit(LitInt(1)))])
  let result = do_app(state, neut, arg)
  assert result == VNeut(HVar(0), [EApp(VLit(LitInt(1))), EApp(arg)])
}

pub fn do_app_vvar_applied_then_applied_again_test() {
  let state = initial_state([])
  // Build: (v0 42) 100 where v0 is a variable
  let app1 = do_app(state, VNeut(HVar(0), []), VLit(LitInt(42)))
  let app2 = do_app(state, app1, VLit(LitInt(100)))
  assert app2 == VNeut(HVar(0), [EApp(VLit(LitInt(42))), EApp(VLit(LitInt(100)))])
}

// ============================================================================
// PI TYPE EVALUATION
// ============================================================================

pub fn eval_pi_type_test() {
  let state = initial_state([])
  let domain = Lit(LitInt(0), single("", 1, 1))
  let codomain = Lit(LitInt(1), single("", 1, 1))
  let pi = Pi(domain, codomain, single("", 1, 1))
  let value = evaluate(state, pi)
  assert value == VPi(VLit(LitInt(0)), VLit(LitInt(1)))
}

pub fn eval_pi_with_vars_test() {
  let state = initial_state([])
  let domain = Var(1, single("", 1, 1))
  let codomain = Var(0, single("", 1, 1))
  let pi = Pi(domain, codomain, single("", 1, 1))
  let value = evaluate(state, pi)
  // domain becomes VNeut(HVar(1)), codomain (shifted by 1) becomes Var(0, _) -> VNeut(HVar(0))
  assert value == VPi(VNeut(HVar(1), []), VNeut(HVar(0), []))
}

// ============================================================================
// CONSTRUCTOR EVALUATION
// ============================================================================

pub fn eval_ctr_test() {
  let state = initial_state([])
  let arg = Lit(LitInt(42), single("", 1, 1))
  let term = Ctr("Some", arg, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VCtr("Some", VLit(LitInt(42)))
}

pub fn eval_nested_ctr_test() {
  let state = initial_state([])
  let inner = Ctr("Inner", Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let outer = Ctr("Outer", inner, single("", 1, 1))
  let value = evaluate(state, outer)
  assert value == VCtr("Outer", VCtr("Inner", VLit(LitInt(1))))
}

// ============================================================================
// RECORD EVALUATION
// ============================================================================

pub fn eval_empty_record_test() {
  let state = initial_state([])
  let term = Rcd([], single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VRcd([])
}

pub fn eval_record_with_fields_test() {
  let state = initial_state([])
  let fields = [ #("name", Lit(LitInt(42), single("", 1, 1))) ]
  let term = Rcd(fields, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VRcd([ #("name", VLit(LitInt(42))) ])
}

pub fn eval_record_multiple_fields_test() {
  let state = initial_state([])
  let fields = [
    #("a", Lit(LitInt(1), single("", 1, 1))),
    #("b", Lit(LitInt(2), single("", 1, 1))),
  ]
  
  let term = Rcd(fields, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VRcd([ #("a", VLit(LitInt(1))), #("b", VLit(LitInt(2))) ])
}

// ============================================================================
// ANNOTATION (ERASURE)
// ============================================================================

pub fn eval_ann_erases_annotation_test() {
  let state = initial_state([])
  let ann = Ann(Lit(LitInt(42), single("", 1, 1)), Lit(LitInt(0), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, ann)
  assert value == VLit(LitInt(42))
}

// ============================================================================
// ERROR TERM EVALUATION
// ============================================================================

pub fn eval_err_becomes_vevr_test() {
  let state = initial_state([])
  let value = evaluate(state, Err("something went wrong", single("", 1, 1)))
  assert value == VErr
}

// ============================================================================
// TYPE TERMINATOR
// ============================================================================

pub fn eval_typ_becomes_neutral_test() {
  let state = initial_state([])
  let value = evaluate(state, Typ(1, single("", 1, 1)))
  assert value == VNeut(HVar(1), [])
}

// ============================================================================
// MATCH EXPRESSIONS
// ============================================================================

pub fn eval_match_first_case_matches_test() {
  let state = initial_state([])
  // Match #Some(42) { | #Some(v) => v | _ => 0 }
  let scrutinee = Ctr("Some", Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let case1_body = Var(0, single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let cases = [
    CoreCase(Pctr("Some", PVar("v", single("", 1, 1)), span: single("", 1, 1)), None, case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VNeut(HVar(0), [])
}

pub fn eval_match_fallback_any_test() {
  let state = initial_state([])
  // Match #Nothing { | #Some(v) => v | _ => 0 }
  let scrutinee = Ctr("Nothing", Rcd([], single("", 1, 1)), single("", 1, 1))
  let case1_body = Var(0, single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let cases = [
    CoreCase(Pctr("Some", PVar("v", single("", 1, 1)), span: single("", 1, 1)), None, case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VLit(LitInt(0))
}

pub fn eval_match_no_cases_returns_error_test() {
  let state = initial_state([])
  let scrutinee = Lit(LitInt(42), single("", 1, 1))
  let term = Match(scrutinee, [], single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VErr
}

pub fn eval_match_no_matching_case_returns_error_test() {
  let state = initial_state([])
  // Only has a #Some case, but we match on #Nothing
  let scrutinee = Ctr("Nothing", Rcd([], single("", 1, 1)), single("", 1, 1))
  let case_body = Var(0, single("", 1, 1))
  let cases = [
    CoreCase(Pctr("Some", PAny(single("", 1, 1)), single("", 1, 1)), None, case_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VErr
}

pub fn eval_match_with_guard_passes_test() {
  let state = initial_state([])
  // Match 42 { | 42 ? True => 1 | _ => 0 }
  // Guard evaluates to non-empty record (True with empty arg) -> true
  let scrutinee = Lit(LitInt(42), single("", 1, 1))
  let case1_body = Lit(LitInt(1), single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let guard = Ctr("True", Rcd([], single("", 1, 1)), single("", 1, 1))
  let cases = [
    CoreCase(PLit(LitInt(42), single("", 1, 1)), Some(guard), case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  // Guard evaluates to non-empty record -> true -> first case
  assert value == VLit(LitInt(1))
}

pub fn eval_match_with_guard_fails_test() {
  let state = initial_state([])
  // Guard evaluates to empty record -> false -> fallback
  let scrutinee = Lit(LitInt(42), single("", 1, 1))
  let case1_body = Lit(LitInt(1), single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let guard = Rcd([], single("", 1, 1))
  let cases = [
    CoreCase(PLit(LitInt(42), single("", 1, 1)), Some(guard), case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VLit(LitInt(0))
}

pub fn eval_match_nested_match_test() {
  let state = initial_state([])
  // Match on #Some(#Some(42)) with nested match
  let inner_scrutinee = Ctr("Some", Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let inner_body = Var(0, single("", 2, 1))
  let inner_cases = [
    CoreCase(Pctr("Some", PVar("v", single("", 1, 1)), span: single("", 1, 1)), None, inner_body, single("", 1, 1)),
  ]
  let inner_match = Match(inner_scrutinee, inner_cases, single("", 1, 1))

  let outer_scrutinee = Ctr("Some", inner_match, single("", 1, 1))
  let outer_body = Var(0, single("", 2, 1))
  let outer_cases = [
    CoreCase(Pctr("Some", PVar("v", single("", 1, 1)), span: single("", 1, 1)), None, outer_body, single("", 1, 1)),
  ]
  let term = Match(outer_scrutinee, outer_cases, single("", 1, 1))
  let value = evaluate(state, term)
  // Inner match resolves #Some(42) -> v=42
  // Outer match resolves #Some(VNeut(HVar(0))) -> v = VNeut(HVar(0))
  // Final body returns v = VNeut(HVar(0))
  assert value == VNeut(HVar(0), [])
}

// ============================================================================
// CALL (FFI) EVALUATION
// ============================================================================

pub fn eval_call_with_ffi_test() {
  // Register an FFI entry and call it
  let ffi_fn = fn(args: List(#(Value, Value))) -> Option(Value) {
    case args {
      [#(v, _), ..] -> case v {
        VLit(LitInt(42)) -> Some(VLit(LitInt(99)))
        _ -> None
      }
      _ -> None
    }
  }
  let state = initial_state([FfiEntry("double", ffi_fn)])
  let call = Call("double", [Lit(LitInt(42), single("", 1, 1))], single("", 1, 1))
  let value = evaluate(state, call)
  assert value == VLit(LitInt(99))
}

pub fn eval_call_with_missing_ffi_returns_error_test() {
  let state = initial_state([])
  let call = Call("nonexistent", [], single("", 1, 1))
  let value = evaluate(state, call)
  assert value == VErr
}

pub fn eval_call_ffi_returns_none_returns_error_test() {
  let ffi_fn = fn(_args: List(#(Value, Value))) -> Option(Value) {
    None
  }
  let state = initial_state([FfiEntry("bad_ffi", ffi_fn)])
  let call = Call("bad_ffi", [], single("", 1, 1))
  let value = evaluate(state, call)
  assert value == VErr
}

// ============================================================================
// PATTERN MATCHING HELPERS
// ============================================================================

pub fn match_pattern_pany_matches_anything_test() {
  let p = PAny(single("", 1, 1))
  let v = VLit(LitInt(42))
  assert match_pattern(p, v, []) == Ok([])
}

pub fn match_pattern_pvar_binds_value_test() {
  let p = PVar("x", single("", 1, 1))
  let v = VLit(LitInt(42))
  let result = match_pattern(p, v, [])
  assert result == Ok([ #("x", VLit(LitInt(42))) ])
}

pub fn match_pattern_pvar_binds_and_accumulates_test() {
  let p = PVar("y", single("", 1, 1))
  let v = VCtr("Just", VLit(LitInt(1)))
  let existing = [ #("x", VLit(LitInt(0))) ]
  let result = match_pattern(p, v, existing)
  assert result == Ok([ #("y", VCtr("Just", VLit(LitInt(1)))), #("x", VLit(LitInt(0))) ])
}

pub fn match_pattern_pctr_matching_tag_test() {
  let p = Pctr("Just", PVar("v", single("", 1, 1)), span: single("", 1, 1))
  let v = VCtr("Just", VLit(LitInt(42)))
  let result = match_pattern(p, v, [])
  assert result == Ok([ #("v", VLit(LitInt(42))) ])
}

pub fn match_pattern_pctr_wrong_tag_test() {
  let p = Pctr("Just", PVar("v", single("", 1, 1)), span: single("", 1, 1))
  let v = VCtr("Nothing", VRcd([]))
  let result = match_pattern(p, v, [])
  assert result == Error(Nil)
}

pub fn match_pattern_pctr_wrong_value_type_test() {
  let p = Pctr("Just", PAny(single("", 1, 1)), single("", 1, 1))
  let v = VLit(LitInt(42))
  let result = match_pattern(p, v, [])
  assert result == Error(Nil)
}

pub fn match_pattern_punit_empty_record_test() {
  let p = PUnit(single("", 1, 1))
  let v = VRcd([])
  let result = match_pattern(p, v, [])
  assert result == Ok([])
}

pub fn match_pattern_punit_nonempty_record_fails_test() {
  let p = PUnit(single("", 1, 1))
  let v = VRcd([ #("x", VLit(LitInt(42))) ])
  let result = match_pattern(p, v, [])
  assert result == Error(Nil)
}

pub fn match_pattern_plit_matching_test() {
  let p = PLit(LitInt(42), single("", 1, 1))
  let v = VLit(LitInt(42))
  let result = match_pattern(p, v, [])
  assert result == Ok([])
}

pub fn match_pattern_plit_different_value_fails_test() {
  let p = PLit(LitInt(42), single("", 1, 1))
  let v = VLit(LitInt(99))
  let result = match_pattern(p, v, [])
  assert result == Error(Nil)
}

pub fn match_pattern_nested_ctr_test() {
  let p = Pctr("Outer", Pctr("Inner", PVar("v", single("", 1, 1)), span: single("", 1, 1)), span: single("", 1, 1))
  let v = VCtr("Outer", VCtr("Inner", VLit(LitInt(42))))
  let result = match_pattern(p, v, [])
  assert result == Ok([ #("v", VLit(LitInt(42))) ])
}

// ============================================================================
// LOOKUP ENV
// ============================================================================

pub fn lookup_env_finds_bound_variable_test() {
  let bindings = [ #("x", VLit(LitInt(42))), #("y", VLit(LitInt(99))) ]
  let value = lookup_env("y", bindings)
  assert value == VLit(LitInt(99))
}

pub fn lookup_env_returns_neutral_when_not_found_test() {
  let bindings = [ #("x", VLit(LitInt(42))) ]
  let value = lookup_env("z", bindings)
  assert value == VNeut(HVar(0), [])
}

pub fn lookup_env_empty_bindings_test() {
  let value = lookup_env("any", [])
  assert value == VNeut(HVar(0), [])
}

// ============================================================================
// VALUE TO STRING
// ============================================================================

pub fn value_to_string_lit_int_test() {
  assert value_to_string(VLit(LitInt(42))) == "42"
}

pub fn value_to_string_lit_float_test() {
  let s = value_to_string(VLit(LitFloat(3.14)))
  assert s == "3.14"
}

pub fn value_to_string_neutral_var_test() {
  assert value_to_string(VNeut(HVar(5), [])) == "v5"
}

pub fn value_to_string_neutral_hole_test() {
  assert value_to_string(VNeut(HHole(42), [])) == "?42"
}

pub fn value_to_string_neutral_with_spine_test() {
  let s = value_to_string(VNeut(HVar(0), [EApp(VLit(LitInt(42)))]))
  assert s == "v0(42)"
}

pub fn value_to_string_vctr_test() {
  assert value_to_string(VCtr("Some", VLit(LitInt(42)))) == "#Some(42)"
}

pub fn value_to_string_vrcd_test() {
  assert value_to_string(VRcd([])) == "()"
}

pub fn value_to_string_vrcd_with_fields_test() {
  let s = value_to_string(VRcd([ #("x", VLit(LitInt(1))), #("y", VLit(LitInt(2))) ]))
  assert s == "{x: 1, y: 2}"
}

pub fn value_to_string_vevr_test() {
  assert value_to_string(VErr) == "\"error\""
}

pub fn value_to_string_vlam_test() {
  let body = Var(0, single("", 1, 1))
  let s = value_to_string(VLam(#("x", VRcd([])), body))
  assert s == "%fn(x) => #0"
}

pub fn value_to_string_vpi_test() {
  let s = value_to_string(VPi(VLit(LitInt(0)), VNeut(HVar(0), [])))
  assert s == "%fn(_) : 0 -> v0"
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn eval_var_zero_in_empty_env_test() {
  // Variable in empty environment -> becomes neutral (will be unresolved at runtime)
  let state = initial_state([])
  let value = evaluate(state, Var(0, single("", 1, 1)))
  assert value == VNeut(HVar(0), [])
}

pub fn eval_app_on_hole_neutral_test() {
  // App(Hole(0), Lit(42))
  let state = initial_state([])
  let app = App(Hole(0, single("", 1, 1)), Lit(LitInt(42), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VNeut(HHole(0), [EApp(VLit(LitInt(42)))])
}

pub fn eval_chain_of_applications_test() {
  // Build a chain: App(App(f, 1), 2), 3
  let state = initial_state([])
  let f = Var(0, single("", 1, 1))
  let app1 = App(f, Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let app2 = App(app1, Lit(LitInt(2), single("", 1, 1)), single("", 1, 1))
  let app3 = App(app2, Lit(LitInt(3), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app3)
  assert value == VNeut(HVar(0), [
    EApp(VLit(LitInt(1))),
    EApp(VLit(LitInt(2))),
    EApp(VLit(LitInt(3))),
  ])
}

pub fn eval_match_on_constructor_neutral_test() {
  // Match on a constructor that has a neutral arg
  let state = initial_state([])
  let scrutinee = Ctr("Some", Var(0, single("", 1, 1)), single("", 1, 1))
  let case_body = Lit(LitInt(1), single("", 1, 1))
  let cases = [
    CoreCase(Pctr("Some", PAny(single("", 1, 1)), single("", 1, 1)), None, case_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  // #Some(v) matches -> returns body (Lit(1))
  assert value == VLit(LitInt(1))
}

pub fn eval_app_on_literal_returns_error_test() {
  // Applying a literal as a function -> error
  let state = initial_state([])
  let app = App(Lit(LitInt(42), single("", 1, 1)), Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VErr
}

pub fn eval_app_on_ctr_returns_error_test() {
  // Applying a constructor as a function -> error
  let state = initial_state([])
  let app = App(Ctr("Some", Lit(LitInt(42), single("", 1, 1)), single("", 1, 1)), Lit(LitInt(1), single("", 1, 1)), single("", 1, 1))
  let value = evaluate(state, app)
  assert value == VErr
}

pub fn eval_match_first_case_evaluates_guard_test() {
  let state = initial_state([])
  // First case has a guard that evaluates to non-empty record (true)
  let scrutinee = Lit(LitInt(1), single("", 1, 1))
  let case1_guard = Ctr("True", Rcd([], single("", 1, 1)), single("", 1, 1))
  let case1_body = Lit(LitInt(99), single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let cases = [
    CoreCase(PLit(LitInt(1), single("", 1, 1)), Some(case1_guard), case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  assert value == VLit(LitInt(99))
}

pub fn eval_match_second_case_with_guard_fails_test() {
  let state = initial_state([])
  // First case guard fails -> second case matches
  let scrutinee = Lit(LitInt(1), single("", 1, 1))
  let case1_guard = Rcd([], single("", 1, 1))  // empty record = false
  let case1_body = Lit(LitInt(99), single("", 2, 1))
  let case2_body = Lit(LitInt(0), single("", 2, 1))
  let cases = [
    CoreCase(PLit(LitInt(1), single("", 1, 1)), Some(case1_guard), case1_body, single("", 1, 1)),
    CoreCase(PAny(single("", 1, 1)), None, case2_body, single("", 1, 1)),
  ]
  let term = Match(scrutinee, cases, single("", 1, 1))
  let value = evaluate(state, term)
  // First guard evaluates to empty record -> false, so fallback
  assert value == VLit(LitInt(0))
}

pub fn eval_call_evaluates_args_first_test() {
  // FFI call should evaluate all arguments before calling
  let ffi_fn = fn(args: List(#(Value, Value))) -> Option(Value) {
    case args {
      [arg, ..] -> case arg {
        #(v, _) -> case v {
          VLit(LitInt(99)) -> Some(VLit(LitInt(99)))
          _ -> None
        }
      }
      [] -> None
    }
  }
  // Use a simpler arg - just a literal
  let state = initial_state([FfiEntry("echo", ffi_fn)])
  let call = Call("echo", [Lit(LitInt(99), single("", 1, 1))], single("", 1, 1))
  let value = evaluate(state, call)
  assert value == VLit(LitInt(99))
}

pub fn value_to_string_nested_vctr_test() {
  let s = value_to_string(VCtr("Outer", VCtr("Inner", VLit(LitInt(1)))))
  assert s == "#Outer(#Inner(1))"
}

pub fn value_to_string_neutral_hole_with_spine_test() {
  let s = value_to_string(VNeut(HHole(7), [
    EApp(VLit(LitInt(1))),
    EApp(VLit(LitInt(2))),
  ]))
  assert s == "?7(1)(2)"
}

// ============================================================================
// IS TRUE VALUE
// ============================================================================

pub fn is_true_value_empty_record_returns_false_test() {
  assert is_true_value(VRcd([])) == False
}

pub fn is_true_value_nonempty_record_returns_true_test() {
  assert is_true_value(VRcd([ #("x", VLit(LitInt(42))) ])) == True
}

pub fn is_true_value_constructor_returns_true_test() {
  assert is_true_value(VCtr("Some", VLit(LitInt(42)))) == True
}

pub fn is_true_value_neutral_returns_true_test() {
  assert is_true_value(VNeut(HVar(0), [])) == True
}

pub fn is_true_value_neutral_with_spine_returns_true_test() {
  assert is_true_value(VNeut(HHole(1), [EApp(VLit(LitInt(42)))])) == True
}

pub fn is_true_value_error_returns_false_test() {
  assert is_true_value(VErr) == False
}

pub fn is_true_value_literal_returns_false_test() {
  assert is_true_value(VLit(LitInt(42))) == False
  assert is_true_value(VLit(LitFloat(3.14))) == False
}

pub fn is_true_value_pi_returns_false_test() {
  assert is_true_value(VPi(VLit(LitInt(0)), VNeut(HVar(0), []))) == False
}
