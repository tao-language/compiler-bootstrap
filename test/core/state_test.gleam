import gleeunit
import gleam/option.{None}
import gleam/list
import core/state.{initial_state, FfiEntry, with_err, def_var, lookup_var, lookup_by_level, new_hole, new_hole_value, with_ffi_entry, lookup_ffi, has_errors, errors, get_vars, error_to_string, truth_ctor, with_truth_ctor, with_max_steps, TypeMismatch, VarUndefined, HoleUnsolved, NotAFunction, CtrUndefined, MatchMissing, MatchRedundant, StepLimitExceeded}
import core/ast.{VNeut, HHole, VUnit}


pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Initial state
// ============================================================================

pub fn initial_state_creates_empty_vars_and_default_truth_test() {
  let state = initial_state([], "True")
  assert state.vars == []
  assert truth_ctor(state) == "True"
}

pub fn initial_state_has_max_steps_test() {
  let state = initial_state([], "True")
  assert state.max_steps == 10000
}

// ============================================================================
// State modification: variables
// ============================================================================

pub fn def_var_adds_variable_to_state_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  assert lookup_var(new_state, "x") == Ok(#(VUnit, VUnit))
}

pub fn lookup_var_returns_error_for_missing_test() {
  let state = initial_state([], "True")
  assert lookup_var(state, "z") == Error(Nil)
}

pub fn lookup_by_level_finds_variable_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  assert lookup_by_level(new_state, 0) == Ok(#(VUnit, VUnit))
}

pub fn lookup_by_level_returns_error_for_missing_test() {
  let state = initial_state([], "True")
  assert lookup_by_level(state, 0) == Error(Nil)
}

pub fn lookup_by_level_handles_multiple_vars_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = def_var(s1, "y", VUnit, VUnit)
  assert lookup_by_level(s2, 0) == Ok(#(VUnit, VUnit))
  assert lookup_by_level(s2, 1) == Ok(#(VUnit, VUnit))
}

pub fn get_vars_returns_variable_list_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = def_var(s1, "y", VUnit, VUnit)
  let vars = get_vars(s2)
  assert list.length(vars) == 2
}

// ============================================================================
// State modification: holes
// ============================================================================

pub fn new_hole_returns_incrementing_id_test() {
  let state = initial_state([], "True")
  let result1 = new_hole(state)
  assert result1.0 == 0
  let result2 = new_hole(result1.1)
  assert result2.0 == 1
}

pub fn new_hole_value_creates_hole_neutral_test() {
  let state = initial_state([], "True")
  let result = new_hole_value(state)
  assert case result {
    #(VNeut(HHole(0), _), _) -> True
    _ -> False
  }
}

// ============================================================================
// State modification: FFI entries
// ============================================================================

pub fn with_ffi_entry_adds_entry_test() {
  let state = initial_state([], "True")
  let entry = FfiEntry("my_ffi", fn(_) { None })
  let new_state = with_ffi_entry(state, entry)
  assert case lookup_ffi(new_state, "my_ffi") {
    Ok(_) -> True
    Error(_) -> False
  }
}

// ============================================================================
// Error handling
// ============================================================================

pub fn with_err_adds_error_to_list_test() {
  let state = initial_state([], "True")
  let new_state = with_err(state, HoleUnsolved(1))
  assert errors(new_state) == [HoleUnsolved(1)]
}

pub fn with_err_preserves_vars_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = with_err(s1, HoleUnsolved(1))
  assert lookup_var(s2, "x") == Ok(#(VUnit, VUnit))
}

pub fn has_errors_returns_false_when_empty_test() {
  let state = initial_state([], "True")
  assert has_errors(state) == False
}

pub fn has_errors_returns_true_when_has_errors_test() {
  let state = with_err(initial_state([], "True"), HoleUnsolved(1))
  assert has_errors(state) == True
}

// ============================================================================
// State modification: truth constructor
// ============================================================================

pub fn truth_ctor_returns_constructor_name_test() {
  let state = initial_state([], "True")
  assert truth_ctor(state) == "True"
}

pub fn with_truth_ctor_updates_constructor_test() {
  let state = initial_state([], "True")
  let new_state = with_truth_ctor(state, "False")
  assert truth_ctor(new_state) == "False"
}

// ============================================================================
// State modification: max steps
// ============================================================================

pub fn with_max_steps_updates_max_steps_test() {
  let state = initial_state([], "True")
  let new_state = with_max_steps(state, 5000)
  assert new_state.max_steps == 5000
}

// ============================================================================
// Error string representation
// ============================================================================

pub fn error_to_string_type_mismatch_test() {
  let err = TypeMismatch(VUnit, VUnit)
  assert error_to_string(err) == "Type mismatch: expected (), got ()"
}

pub fn error_to_string_var_undefined_test() {
  let err = VarUndefined("x")
  assert error_to_string(err) == "Undefined variable: x"
}

pub fn error_to_string_hole_unsolved_test() {
  let err = HoleUnsolved(1)
  assert error_to_string(err) == "Unsolved hole: ?1"
}

pub fn error_to_string_not_a_function_test() {
  let err = NotAFunction(VUnit)
  assert error_to_string(err) == "Not a function: ()"
}

pub fn error_to_string_ctr_undefined_test() {
  let err = CtrUndefined("my_ffi")
  assert error_to_string(err) == "Undefined constructor: my_ffi"
}

pub fn error_to_string_match_missing_test() {
  let err = MatchMissing(["x"], ["x"])
  assert error_to_string(err) == "Missing match cases. Patterns not covered: x. Covered: x"
}

pub fn error_to_string_match_redundant_test() {
  let err = MatchRedundant
  assert error_to_string(err) == "Redundant match case"
}

pub fn error_to_string_step_limit_test() {
  let err = StepLimitExceeded(10000)
  assert error_to_string(err) == "Step limit exceeded (10000 steps)"
}
