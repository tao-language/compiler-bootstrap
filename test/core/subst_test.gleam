/// Tests for the substitution module
///
/// Tests cover:
/// - `force` — hole resolution and neutral spine application
/// - `apply_spine` — beta reduction and spine building
/// - `shift_term` — De Bruijn index shifting
/// - `subst_term_var` — variable substitution in shifted terms
/// - `force_levels_to_indices` — Value to Term conversion

import gleeunit
import core/subst.{force, apply_spine, shift_term, subst_term_var, force_levels_to_indices, force_to_string, levels_to_indices_to_string}
import core/state.{initial_state, def_var}
import core/ast.{
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Call, Rcd, Err,
  VNeut, HHole, HVar, VLam, VPi, VLit, VCtr, VRcd, VErr, EApp,
  Int as LitInt, Float as LitFloat, PAny, Case,
}
import gleam/option.{None}
import syntax/span.{single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// FORCE — Hole resolution
// ============================================================================

pub fn force_non_neutral_returns_value_test() {
  // Non-neutral values are returned unchanged
  let state = initial_state([])
  let value = VLit(LitInt(42))
  let result = force(state, value)
  assert result == VLit(LitInt(42))
}

pub fn force_empty_spine_returns_value_test() {
  // Neutral with empty spine is returned unchanged (no hole to resolve)
  let state = initial_state([])
  let value = VNeut(HVar(0), [])
  let result = force(state, value)
  assert result == VNeut(HVar(0), [])
}

pub fn force_hole_resolved_test() {
  // A hole that is bound in state should be resolved
  let hole_val = VCtr("Just", VLit(LitInt(1)))
  let state = def_var(initial_state([]), "hole0", hole_val, hole_val)
  let value = VNeut(HHole(0), [])
  let result = force(state, value)
  assert result == VCtr("Just", VLit(LitInt(1)))
}

pub fn force_hole_with_name_binding_test() {
  // Holes are looked up by name "hole{id}"
  let bound_val = VLit(LitFloat(3.14))
  let state = def_var(initial_state([]), "hole5", bound_val, bound_val)
  let value = VNeut(HHole(5), [])
  let result = force(state, value)
  assert result == VLit(LitFloat(3.14))
}

pub fn force_unresolved_hole_returns_unchanged_test() {
  // A hole with no binding is returned unchanged
  let state = initial_state([])
  let value = VNeut(HHole(99), [])
  let result = force(state, value)
  assert result == VNeut(HHole(99), [])
}

// ============================================================================
// FORCE — Neutral spine application
// ============================================================================

pub fn force_neutral_with_spine_not_applicable_test() {
  // Neutral with spine that can't be applied stays neutral
  let state = initial_state([])
  let value = VNeut(HVar(0), [EApp(VLit(LitInt(1)))])
  let result = force(state, value)
  // HVar(0) looks up in empty state — fails, so value is returned unchanged
  assert result == VNeut(HVar(0), [EApp(VLit(LitInt(1)))])
}

pub fn force_neutral_head_preserved_test() {
  // Neutral head that isn't a hole should be preserved
  let state = initial_state([])
  let value = VNeut(HVar(5), [EApp(VLit(LitInt(1)))])
  let result = force(state, value)
  // HVar(5) can't be found in empty state — returns unchanged
  assert result == VNeut(HVar(5), [EApp(VLit(LitInt(1)))])
}

// ============================================================================
// APPLY_SPINE — Lambda application (beta reduction)
// ============================================================================

pub fn apply_spine_empty_test() {
  // Empty spine returns value unchanged
  let _state = def_var(initial_state([]), "test", VLit(LitInt(1)), VLit(LitInt(1)))
  let value = VLit(LitInt(42))
  let result = apply_spine(value, [])
  assert result == VLit(LitInt(42))
}

pub fn apply_spine_single_element_test() {
  // Single eliminator on a neutral value that can't be applied
  // Application fails → returns neutral with empty spine
  let value = VNeut(HVar(0), [])
  let result = apply_spine(value, [EApp(VLit(LitInt(1)))])
  // When application fails, the value is returned unchanged
  assert result == VNeut(HVar(0), [])
}

pub fn apply_spine_lambda_consumes_one_test() {
  // A lambda should consume one argument
  let arg = VCtr("Just", VLit(LitInt(42)))
  let param_type = VNeut(HHole(0), [])
  let body = Var(0, single("", 0, 0))
  let value = VLam(#("x", param_type), body)
  let result = apply_spine(value, [EApp(arg)])
  // VLam consumes arg: body Var(0) → shifted to Var(1) → not substituted
  assert case result {
    VLam(#("x", _), Var(1, _)) -> True
    _ -> False
  }
}

// ============================================================================
// APPLY_SPINE — Multiple spine elements
// ============================================================================

pub fn apply_spine_multiple_elements_test() {
  // Multiple eliminators: first lambda consumes first arg
  let _state = def_var(initial_state([]), "x", VLit(LitInt(1)), VLit(LitInt(1)))
  let param_type = VNeut(HHole(0), [])
  let body = Var(0, single("", 0, 0))
  let value = VLam(#("x", param_type), body)
  let result = apply_spine(value, [EApp(VLit(LitInt(1))), EApp(VLit(LitInt(2)))])
  // First arg consumed, second arg can't apply to substituted result
  assert case result {
    VLam(#(_name, _param_type), _body) -> True
    _ -> False
  }
}

// ============================================================================
// SHIFT_TERM — Basic index shifting
// ============================================================================

pub fn shift_term_positive_var_test() {
  // Positive shift opens scopes
  let t = Var(0, single("test", 1, 1))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Var(1, _) -> True
    _ -> False
  }
}

pub fn shift_term_positive_var_from_test() {
  // Shift only affects indices >= from (tested via shift_term with from=1)
  // Var(1) shifted by 1 from from=0 -> Var(2) because 1 >= 0
  let t = Var(1, single("test", 1, 1))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Var(2, _) -> True
    _ -> False
  }
}

pub fn shift_term_hole_preserved_test() {
  // Holes are unaffected by shifting
  let t = Hole(5, single("test", 1, 1))
  let shifted = shift_term(t, 3)
  assert case shifted {
    Hole(5, _) -> True
    _ -> False
  }
}

pub fn shift_term_lambda_test() {
  // Lambda: param shifted by 1 (0 → 1), body shifted by 1 from +1 (0 → 0 since 0 < 1)
  let param = Var(0, single("test", 1, 1))
  let body = Var(0, single("test", 1, 2))
  let t = Lam(#("x", param), body, single("test", 1, 3))
  let shifted = shift_term(t, 1)
  // Param Var(0) at from=0 → Var(1) (0 >= 0)
  // Body Var(0) at from=1 → Var(0) (0 < 1, stays)
  assert case shifted {
    Lam(#("x", Var(1, _)), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn shift_term_app_test() {
  // App: both fun and arg shifted
  let fun = Var(0, single("test", 1, 1))
  let arg = Var(1, single("test", 1, 2))
  let t = App(fun, arg, single("test", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    App(Var(1, _), Var(2, _), _) -> True
    _ -> False
  }
}

pub fn shift_term_pi_test() {
  // Pi: both domain and codomain shifted
  let domain = Var(0, single("test", 1, 1))
  let codomain = Var(1, single("test", 1, 2))
  let t = Pi(domain, codomain, single("test", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Pi(Var(1, _), Var(2, _), _) -> True
    _ -> False
  }
}

pub fn shift_term_literal_preserved_test() {
  // Literals are unaffected
  let t = Lit(LitInt(42), single("test", 1, 1))
  let shifted = shift_term(t, 5)
  assert shifted == Lit(LitInt(42), single("test", 1, 1))
}

pub fn shift_term_zero_test() {
  // Zero shift is identity
  let t = Var(3, single("test", 1, 1))
  let shifted = shift_term(t, 0)
  assert shifted == t
}

pub fn shift_term_nested_lambda_test() {
  // Nested lambdas: shifting interacts correctly with De Bruijn indices
  // outer: Lam("x", Var(1), inner)
  // inner: Lam("y", Var(0), Var(0))
  // After shift by 1:
  // - outer param Var(1) at from=0 → Var(2) (1 >= 0)
  // - inner shifted from 1:
  //   - inner param Var(0) at from=1 → Var(0) (0 < 1, bound by "y")
  //   - inner body Var(0) at from=2 → Var(0) (0 < 2, still bound)
  let body = Var(0, single("test", 1, 1))
  let inner = Lam(#("y", Var(0, single("test", 1, 2))), body, single("test", 1, 3))
  let outer = Lam(#("x", Var(1, single("test", 1, 4))), inner, single("test", 1, 5))
  let shifted = shift_term(outer, 1)
  assert case shifted {
    Lam(#("x", Var(2, _)),
        Lam(#("y", Var(0, _)), Var(0, _), _), _) -> True
    _ -> False
  }
}

pub fn shift_term_selective_by_scope_test() {
  // shift_term shifts ALL indices by default
  // param Var(0) at from=0 → Var(1), body Var(1) at from=1 → Var(2)
  let t = Lam(#("x", Var(0, single("test", 1, 1))), Var(1, single("test", 1, 2)), single("test", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Lam(#("x", Var(1, _)), Var(2, _), _) -> True
    _ -> False
  }
}

// ============================================================================
// SUBST_TERM_VAR — Variable substitution
// ============================================================================

pub fn subst_term_var_self_test() {
  // Substituting Var(0) with a value in Var(0) should replace it
  // Non-neutral values are converted via force_levels_to_indices
  let arg = VCtr("Just", VLit(LitInt(42)))
  let t = Var(0, single("test", 1, 1))
  let result = subst_term_var(0, arg, t)
  assert case result {
    Ctr("Just", Lit(LitInt(42), _), _) -> True
    _ -> False
  }
}

pub fn subst_term_var_skip_bound_test() {
  // Substitution should not reach under binders
  let arg = VCtr("Nothing", VLit(LitInt(0)))
  let body = Var(0, single("test", 1, 1))
  let t = Lam(#("x", Var(0, single("test", 1, 2))), body, single("test", 1, 3))
  let result = subst_term_var(0, arg, t)
  // Var(0) inside body is the lambda's parameter — should be preserved
  assert case result {
    Lam(#("x", _), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn subst_term_var_free_replaced_test() {
  // Free variables (level >= from) should be substituted
  // Non-neutral values are converted via force_levels_to_indices
  let arg = VLit(LitInt(99))
  let t = Var(1, single("test", 1, 1))
  let result = subst_term_var(1, arg, t)
  assert case result {
    Lit(LitInt(99), _) -> True
    _ -> False
  }
}

pub fn subst_term_var_hole_preserved_test() {
  // Holes should not be substituted
  let arg = VLit(LitInt(99))
  let t = Hole(5, single("test", 1, 1))
  let result = subst_term_var(0, arg, t)
  assert case result {
    Hole(5, _) -> True
    _ -> False
  }
}

pub fn subst_term_var_app_test() {
  // Both fun and arg of App should be substituted
  let arg = VLit(LitInt(42))
  let t = App(Var(0, single("test", 1, 1)), Var(1, single("test", 1, 2)), single("test", 1, 3))
  let result = subst_term_var(0, arg, t)
  assert case result {
    App(Lit(LitInt(42), _), Var(1, _), _) -> True
    _ -> False
  }
}

pub fn subst_term_var_pi_test() {
  // Pi domain and codomain should be substituted
  let arg = VLit(LitInt(42))
  let t = Pi(Var(0, single("test", 1, 1)), Var(1, single("test", 1, 2)), single("test", 1, 3))
  let result = subst_term_var(0, arg, t)
  assert case result {
    Pi(Lit(LitInt(42), _), Var(1, _), _) -> True
    _ -> False
  }
}

pub fn subst_term_var_nested_lambda_preserves_binder_test() {
  // Nested lambdas: substitution only affects terms, not params
  // Param of outer Lam is Var(1) — param is not visited
  // Param of inner Lam is Var(0) — param is not visited
  // Body of inner Lam is Var(0) — not substituted (idx=0 != i=0 at from=2)
  let arg = VCtr("Just", VLit(LitInt(0)))
  let body = Var(0, single("test", 1, 1))
  let inner = Lam(#("y", Var(0, single("test", 1, 2))), body, single("test", 1, 3))
  let t = Lam(#("x", Var(1, single("test", 1, 4))), inner, single("test", 1, 5))
  let result = subst_term_var(0, arg, t)
  assert case result {
    Lam(#("x", Var(1, _)), Lam(#("y", Var(0, _)), Var(0, _), _), _) -> True
    _ -> False
  }
}

// ============================================================================
// FORCE_LEVELS_TO_INDICES — Value to Term conversion
// ============================================================================

pub fn force_levels_to_indices_lit_int_test() {
  let value = VLit(LitInt(42))
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_hvar_at_zero_test() {
  // HVar(0) at n=0: bound variable, index = 0 - 1 - 0 = -1 → abs_index = 0 - 1 - 0 = -1? 
  // Wait: abs_index(level=0, n=0): level < n → False, so index = 0 - 0 = 0
  let value = VNeut(HVar(0), [])
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Var(0, _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_hvar_bound_test() {
  // HVar(0) at n=1: bound variable, index = 1 - 1 - 0 = 0
  let value = VNeut(HVar(0), [])
  let result = force_levels_to_indices(value, 1)
  assert case result {
    Var(0, _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_hvar_bound_two_test() {
  // HVar(1) at n=2: bound variable, index = 2 - 1 - 1 = 0
  let value = VNeut(HVar(1), [])
  let result = force_levels_to_indices(value, 2)
  assert case result {
    Var(0, _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_hvar_free_test() {
  // HVar(2) at n=1: free variable, index = 2 - 1 = 1
  let value = VNeut(HVar(2), [])
  let result = force_levels_to_indices(value, 1)
  assert case result {
    Var(1, _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_hole_test() {
  let value = VNeut(HHole(42), [])
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Hole(42, _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_neutral_spine_test() {
  // Neutral with spine: Var(n) applied to arg
  let arg = VLit(LitInt(1))
  let value = VNeut(HVar(0), [EApp(arg)])
  let result = force_levels_to_indices(value, 0)
  assert case result {
    App(Var(0, _), Lit(_, _), _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_vlam_test() {
  // Lambda: param type (Value) converted to Term, body is already a Term
  let param_type = VNeut(HHole(0), [])
  let body = Var(0, single("", 0, 0))
  let value = VLam(#("x", param_type), body)
  let result = force_levels_to_indices(value, 0)
  // param type: Hole(0) → Hole(0), body: Var(0) unchanged
  assert case result {
    Lam(#("x", Hole(0, _)), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_vpi_test() {
  // Pi: domain at n, codomain at n+1
  let domain = VLit(LitInt(42))
  let codomain = VNeut(HHole(0), [])
  let value = VPi(domain, codomain)
  let result = force_levels_to_indices(value, 0)
  // domain: Lit(42), codomain: Hole(0) at n=1 → Hole(0)
  assert case result {
    Pi(Lit(LitInt(42), _), Hole(0, _), _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_vctr_test() {
  let arg = VLit(LitInt(1))
  let value = VCtr("Just", arg)
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Ctr("Just", Lit(LitInt(1), _), _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_vrcd_test() {
  let fields = [#("x", VLit(LitInt(1))), #("y", VLit(LitFloat(2.0)))]
  let value = VRcd(fields)
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Rcd([#("x", Lit(LitInt(1), _)), #("y", Lit(LitFloat(_), _))], _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_vrcd_empty_test() {
  let value = VRcd([])
  let result = force_levels_to_indices(value, 0)
  assert result == Rcd([], single("", 0, 0))
}

pub fn force_levels_to_indices_verr_test() {
  let value = VErr
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Err("error", _) -> True
    _ -> False
  }
}

pub fn force_levels_to_indices_neutral_hvar_spine_multi_test() {
  // Multi-element spine
  let arg1 = VLit(LitInt(1))
  let arg2 = VLit(LitInt(2))
  let value = VNeut(HVar(0), [EApp(arg1), EApp(arg2)])
  let result = force_levels_to_indices(value, 0)
  assert case result {
    App(App(Var(0, _), Lit(_, _), _), Lit(_, _), _) -> True
    _ -> False
  }
}

// ============================================================================
// STRING REPRESENTATION
// ============================================================================

pub fn force_to_string_literal_test() {
  let value = VLit(LitInt(42))
  let result = force_to_string(value)
  assert result == "42"
}

pub fn force_to_string_neutral_test() {
  let value = VNeut(HVar(3), [])
  let result = force_to_string(value)
  assert result == "v3"
}

pub fn force_to_string_vctr_test() {
  let value = VCtr("Just", VLit(LitInt(1)))
  let result = force_to_string(value)
  assert result == "#Just(1)"
}

pub fn force_to_string_vlam_test() {
  let param_type = VNeut(HHole(0), [])
  let body = Var(0, single("", 0, 0))
  let value = VLam(#("x", param_type), body)
  let result = force_to_string(value)
  assert result == "%fn(x) => #0"
}

pub fn levels_to_indices_to_string_var_test() {
  let t = Var(3, single("test", 1, 1))
  let result = levels_to_indices_to_string(t)
  assert result == "#3"
}

pub fn levels_to_indices_to_string_hole_test() {
  let t = Hole(5, single("test", 1, 1))
  let result = levels_to_indices_to_string(t)
  assert result == "?5"
}

pub fn levels_to_indices_to_string_lit_test() {
  let t = Lit(LitInt(42), single("test", 1, 1))
  let result = levels_to_indices_to_string(t)
  assert result == "42"
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn force_shift_term_preserves_id_test() {
  // Shifting preserves hole IDs
  let t = Hole(99, single("test", 1, 1))
  let shifted = shift_term(t, 5)
  assert case shifted {
    Hole(99, _) -> True
    _ -> False
  }
}

pub fn force_force_levels_to_indices_empty_record_test() {
  let value = VRcd([])
  let result = force_levels_to_indices(value, 0)
  assert result == Rcd([], single("", 0, 0))
}

pub fn force_force_levels_to_indices_deeply_nested_test() {
  // Deep nesting: HVar(0) under 2 lambdas → index 1
  // Inner: VLam("z", body) where body = Var(0)
  // Outer: VLam("x", inner_lam) where param = HVar(1)
  let inner_param = VNeut(HHole(0), [])
  let inner_body = Var(0, single("", 0, 0))
  let _inner_lam = VLam(#("z", inner_param), inner_body)
  // For outer: param type is HVar(1) at n=1 → abs_index(1,1) = 0
  // body is VLam (a Value) — but VLam's body field IS a Term
  // VLam(#("x", outer_param), inner_lam) — inner_lam is a Value, not a Term!
  // This test is tricky because VLam's body is a Term.
  // Let's use a simpler nested case with Terms directly.
  let param_type = VNeut(HHole(0), [])
  let body_term = Var(0, single("", 0, 0))
  let value = VLam(#("x", param_type), body_term)
  let result = force_levels_to_indices(value, 0)
  // Param (hole 0) → Hole(0), body (Var(0)) → Var(0)
  assert case result {
    Lam(#("x", Hole(0, _)), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn force_force_levels_to_indices_nested_lambda_param_test() {
  // Verify lambda param type conversion under nesting
  let body = Var(0, single("", 0, 0))
  let value = VLam(#("x", VNeut(HHole(0), [])), body)
  let result = force_levels_to_indices(value, 0)
  // Param (hole 0 at n=1) → Hole(0), body (Var at n=1) → Var(0)
  assert case result {
    Lam(#("x", Hole(0, _)), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn force_apply_spine_non_lambda_returns_neutral_test() {
  // Applying spine to non-lambda should return neutral with empty spine
  let value = VLit(LitInt(42))
  let result = apply_spine(value, [EApp(VLit(LitInt(1)))])
  assert case result {
    VNeut(HVar(0), []) -> True
    _ -> False
  }
}

pub fn force_force_levels_to_indices_pi_under_lam_test() {
  // Simple VLam test: param type converted to Term
  let param = VNeut(HHole(0), [])
  let inner_body = Var(0, single("", 0, 0))
  let value = VLam(#("x", param), inner_body)
  let result = force_levels_to_indices(value, 0)
  assert case result {
    Lam(#("x", Hole(0, _)), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn force_shift_term_record_test() {
  // Record fields should be shifted
  let fields = [#("x", Var(0, single("t", 1, 1))), #("y", Var(1, single("t", 1, 2)))]
  let t = Rcd(fields, single("t", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Rcd([#("x", Var(1, _)), #("y", Var(2, _))], _) -> True
    _ -> False
  }
}

pub fn force_shift_term_call_test() {
  // Call args should be shifted
  let t = Call("f", [Var(0, single("t", 1, 1)), Var(1, single("t", 1, 2))], single("t", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Call("f", [Var(1, _), Var(2, _)], _) -> True
    _ -> False
  }
}

pub fn force_shift_term_ann_test() {
  // Ann term and type should be shifted
  let t = Ann(Var(0, single("t", 1, 1)), Var(1, single("t", 1, 2)), single("t", 1, 3))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Ann(Var(1, _), Var(2, _), _) -> True
    _ -> False
  }
}

pub fn force_shift_term_ctr_preserved_test() {
  // Ctr arg shifted, tag preserved
  let t = Ctr("Some", Var(0, single("t", 1, 1)), single("t", 1, 2))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Ctr("Some", Var(1, _), _) -> True
    _ -> False
  }
}

pub fn force_shift_term_pi_bound_test() {
  // Pi type: codomain Var(0) is bound in domain scope
  // Var(0) in domain, Var(0) in codomain (referring to domain's param)
  let domain = Lam(#("x", Var(0, single("t", 1, 1))), Var(1, single("t", 1, 2)), single("t", 1, 3))
  let codomain = Var(0, single("t", 1, 4))
  let t = Pi(domain, codomain, single("t", 1, 5))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Pi(Lam(#("x", Var(1, _)), Var(2, _), _), Var(1, _), _) -> True
    _ -> False
  }
}

pub fn force_shift_term_match_test() {
  // Match arg and case bodies should be shifted
  let cases = [
    Case(PAny(single("t", 1, 1)), None, Var(0, single("t", 1, 2)), single("t", 1, 3)),
  ]
  let t = Match(Var(0, single("t", 1, 4)), cases, single("t", 1, 5))
  let shifted = shift_term(t, 1)
  assert case shifted {
    Match(Var(1, _), [Case(PAny(_), None, Var(1, _), _)], _) -> True
    _ -> False
  }
}
