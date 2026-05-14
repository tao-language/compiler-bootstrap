/// Tests for the unification module
///
/// Tests cover:
/// - Basic value equality (same types)
/// - Hole binding (HHole → concrete value)
/// - Hole already bound (re-unification)
/// - Variable lookup (HVar → bound value)
/// - Pi type unification
/// - Lambda type unification
/// - Constructor tag mismatch
/// - Literal value mismatch
/// - Record field mismatch
/// - Record matching
/// - Neutral term comparison
/// - Error accumulation
/// - VErr passthrough (err type unifies with anything)
/// - occurs_check always allows recursive types
import core/ast.{
  type Value, type Term,
  EApp, Float as LitFloat, HHole, HVar, Int as LitInt, VCtr, VErr, VLam, VLit,
  VNeut, VPi, VRcd, Var,
  IntT, FloatT, I32T, F64T, VLitT, U32T, U64T,
}
import core/state.{type State, TypeMismatch, def_var, initial_state}
import core/unify.{is_wildcard, literal_type_matches_wildcard, occurs_check, unify}
import gleam/list
import gleeunit
import syntax/span.{single}

// Dummy infer function for tests that don't need inference
fn dummy_infer(_state: State, _term: Term) -> #(Value, Value, State) {
  let state = initial_state([])
  #(VErr, VErr, state)
}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Basic value equality — same types unify successfully
// ============================================================================

pub fn unify_same_lit_int_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VLit(LitInt(42)), VLit(LitInt(42)), dummy_infer)
  assert final.errors == []
}

pub fn unify_same_lit_float_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VLit(LitFloat(3.14)), VLit(LitFloat(3.14)), dummy_infer)
  assert final.errors == []
}

pub fn unify_same_vctr_test() {
  let state = initial_state([])
  let #( _, final) =
    unify(
      state,
      VCtr("Just", VNeut(HVar(0), [])),
      VCtr("Just", VNeut(HVar(0), [])),
      dummy_infer,
    )
  assert final.errors == []
}

pub fn unify_same_vrcd_empty_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VRcd([]), VRcd([]), dummy_infer)
  assert final.errors == []
}

// ============================================================================
// Hole binding — HHole binds to the other value
// ============================================================================

pub fn unify_hole_bounds_to_int_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)), dummy_infer)
  // Hole is bound — no errors
  assert final.errors == []
}

pub fn unify_hole_in_actual_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VLit(LitInt(42)), VNeut(HHole(0), []), dummy_infer)
  assert final.errors == []
}

pub fn unify_same_hole_id_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VNeut(HHole(5), []), VNeut(HHole(5), []), dummy_infer)
  assert final.errors == []
}

pub fn unify_different_hole_ids_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VNeut(HHole(1), []), VNeut(HHole(2), []), dummy_infer)
  // Different holes are treated as different values
  assert list.length(final.errors) >= 1
}

pub fn unify_hole_reunification_test() {
  let state = initial_state([])
  let #( _, s1) = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)), dummy_infer)
  // Re-unify the same hole — should succeed (already bound to 42)
  let #( _, s2) = unify(s1, VNeut(HHole(0), []), VLit(LitInt(42)), dummy_infer)
  assert s2.errors == []
}

pub fn unify_var_lookup_test() {
  let state = initial_state([])
  let state = def_var(state, "test", VLit(LitInt(42)), VLitT(IntT))
  let #( _, final) = unify(state, VNeut(HVar(0), []), VLit(LitInt(42)), dummy_infer)
  assert final.errors == []
}

pub fn unify_var_lookup_unbound_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VNeut(HVar(1), []), VLit(LitInt(42)), dummy_infer)
  assert list.length(final.errors) >= 1
}

pub fn unify_pi_type_test() {
  let state = initial_state([])
  let dom = VNeut(HVar(0), [])
  let codom = VNeut(HVar(1), [])
  let #( _, final) = unify(
    state,
    VPi([], [], #("pi_param", dom), codom),
    VPi([], [], #("pi_param", dom), codom),
    dummy_infer,
  )
  assert final.errors == []
}

pub fn unify_lambda_type_test() {
  let state = initial_state([])
  let param = #("param", VNeut(HVar(0), []))
  let #( _, final) = unify(
    state,
    VLam([], [], param, Var(0, single("", 0, 0))),
    VLam([], [], param, Var(0, single("", 0, 0))),
    dummy_infer,
  )
  assert final.errors == []
}

pub fn unify_ctr_tag_mismatch_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VCtr("Foo", VNeut(HVar(0), [])),
    VCtr("Bar", VNeut(HVar(0), [])),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_lit_mismatch_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitInt(43)),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_lit_mismatch_int_float_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitFloat(42.0)),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_rcd_field_mismatch_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VRcd([#("x", VLit(LitInt(42)))]),
    VRcd([#("x", VLit(LitInt(43)))]),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_rcd_matching_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VRcd([#("x", VLit(LitInt(42)))]),
    VRcd([#("x", VLit(LitInt(42)))]),
    dummy_infer,
  )
  assert final.errors == []
}

pub fn unify_neutral_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VNeut(HVar(0), [EApp(VLit(LitInt(42)))]),
    VNeut(HVar(0), [EApp(VLit(LitInt(42)))]),
    dummy_infer,
  )
  assert final.errors == []
}

pub fn unify_neutral_different_spines_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VNeut(HVar(0), [EApp(VLit(LitInt(42)))]),
    VNeut(HVar(0), [EApp(VLit(LitInt(43)))]),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}

pub fn unify_err_passthrough_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VErr, VLit(LitInt(42)), dummy_infer)
  assert final.errors == []
}

pub fn unify_err_passthrough_other_test() {
  let state = initial_state([])
  let #( _, final) = unify(state, VLit(LitInt(42)), VErr, dummy_infer)
  assert final.errors == []
}

// ============================================================================
// occurs_check always allows recursive types
// ============================================================================

pub fn occurs_check_returns_false_test() {
  let state = initial_state([])
  let v = VNeut(HHole(0), [EApp(VNeut(HHole(0), []))])
  assert occurs_check(0, v) == False
}

// ============================================================================
// Wildcard literal type tests
// ============================================================================

pub fn is_wildcard_int_test() {
  assert is_wildcard(VLitT(IntT)) == True
}

pub fn is_wildcard_float_test() {
  assert is_wildcard(VLitT(FloatT)) == True
}

pub fn is_wildcard_specific_test() {
  assert is_wildcard(VLitT(I32T)) == False
  assert is_wildcard(VLitT(F64T)) == False
}

pub fn literal_type_matches_wildcard_int_to_int_test() {
  assert literal_type_matches_wildcard(IntT, IntT) == True
}

pub fn literal_type_matches_wildcard_int_to_i32_test() {
  assert literal_type_matches_wildcard(IntT, I32T) == True
}

pub fn literal_type_matches_wildcard_int_to_u32_test() {
  assert literal_type_matches_wildcard(IntT, U32T) == True
}

pub fn literal_type_matches_wildcard_float_to_float_test() {
  assert literal_type_matches_wildcard(FloatT, FloatT) == True
}

pub fn literal_type_matches_wildcard_float_to_f64_test() {
  assert literal_type_matches_wildcard(FloatT, F64T) == True
}

pub fn literal_type_matches_wildcard_float_to_int_test() {
  // FloatT matches IntT (for integer literals)
  assert literal_type_matches_wildcard(FloatT, IntT) == True
}

pub fn literal_type_matches_wildcard_specific_to_wildcard_test() {
  // Specific types don't match wildcard in reverse
  assert literal_type_matches_wildcard(I32T, IntT) == False
  assert literal_type_matches_wildcard(F64T, FloatT) == False
}
