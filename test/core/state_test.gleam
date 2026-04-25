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

pub fn initial_state_creates_state_with_empty_vars_and_errors_test() {
  let state = initial_state([], "True")
  case state.vars {
    [] -> True
    _ -> False
  }
}

pub fn initial_state_has_max_steps_10000_test() {
  let state = initial_state([], "True")
  state.max_steps == 10000
}

pub fn initial_state_has_truth_ctor_test() {
  let state = initial_state([], "True")
  case truth_ctor(state) {
    "True" -> True
    _ -> False
  }
}

// ============================================================================
// State modification: variables
// ============================================================================

pub fn def_var_adds_variable_to_state_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  case lookup_var(new_state, "x") {
    Ok(_) -> True
    Error(_) -> False
  }
}

pub fn def_var_returns_new_state_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  case new_state.vars {
    [#("x", #(VUnit, VUnit)), ..] -> True
    _ -> False
  }
}

pub fn lookup_var_finds_existing_variable_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  lookup_var(new_state, "x") == Ok(#(VUnit, VUnit))
}

pub fn lookup_var_returns_none_for_missing_test() {
  let state = initial_state([], "True")
  lookup_var(state, "z") == Error(Nil)
}

pub fn lookup_by_level_finds_by_level_test() {
  let state = initial_state([], "True")
  let new_state = def_var(state, "x", VUnit, VUnit)
  lookup_by_level(new_state, 0) == Ok(#(VUnit, VUnit))
}

pub fn lookup_by_level_returns_none_for_missing_test() {
  let state = initial_state([], "True")
  lookup_by_level(state, 0) == Error(Nil)
}

pub fn lookup_by_level_handles_multiple_vars_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = def_var(s1, "y", VUnit, VUnit)
  lookup_by_level(s2, 0) == Ok(#(VUnit, VUnit))
  && lookup_by_level(s2, 1) == Ok(#(VUnit, VUnit))
}

// ============================================================================
// State modification: holes
// ============================================================================

pub fn new_hole_creates_unique_hole_test() {
  let state = initial_state([], "True")
  let result = new_hole(state)
  result.0 == 1
}

pub fn new_hole_value_creates_unique_hole_value_test() {
  let state = initial_state([], "True")
  let result = new_hole_value(state)
  case result {
    #(VNeut(HHole(1), _), _) -> True
    _ -> False
  }
}

pub fn new_hole_increments_counter_test() {
  let state = initial_state([], "True")
  let result1 = new_hole(state)
  let state1 = result1.1
  let result2 = new_hole(state1)
  result2.0 == 2
}

// ============================================================================
// State modification: FFI entries
// ============================================================================

pub fn with_ffi_entry_adds_entry_test() {
  let state = initial_state([], "True")
  let entry = FfiEntry("my_ffi", fn(_) { None })
  let new_state = with_ffi_entry(state, entry)
  case lookup_ffi(new_state, "my_ffi") {
    Ok(_) -> True
    Error(_) -> False
  }
}

// ============================================================================
// Error handling
// ============================================================================

pub fn with_err_adds_error_test() {
  let state = initial_state([], "True")
  let new_state = with_err(state, HoleUnsolved(1))
  case errors(new_state) {
    [HoleUnsolved(1)] -> True
    _ -> False
  }
}

pub fn with_err_preserves_state_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = with_err(s1, HoleUnsolved(1))
  lookup_var(s2, "x") == Ok(#(VUnit, VUnit))
}

pub fn has_errors_returns_false_when_empty_test() {
  let state = initial_state([], "True")
  has_errors(state) == False
}

pub fn has_errors_returns_true_when_has_errors_test() {
  let state = with_err(initial_state([], "True"), HoleUnsolved(1))
  has_errors(state) == True
}

pub fn get_vars_returns_list_test() {
  let state = initial_state([], "True")
  let s1 = def_var(state, "x", VUnit, VUnit)
  let s2 = def_var(s1, "y", VUnit, VUnit)
  list.length(get_vars(s2)) == 2
}

// ============================================================================
// State modification: truth constructor
// ============================================================================

pub fn truth_ctor_returns_constructor_name_test() {
  let state = initial_state([], "True")
  truth_ctor(state) == "True"
}

pub fn with_truth_ctor_updates_constructor_test() {
  let state = initial_state([], "True")
  let new_state = with_truth_ctor(state, "False")
  truth_ctor(new_state) == "False"
}

// ============================================================================
// State modification: max steps
// ============================================================================

pub fn with_max_steps_updates_max_steps_test() {
  let state = initial_state([], "True")
  let new_state = with_max_steps(state, 5000)
  new_state.max_steps == 5000
}

// ============================================================================
// Error string representation
// ============================================================================

pub fn error_to_string_type_mismatch_test_test() {
  let err = TypeMismatch(VUnit, VUnit)
  error_to_string(err) == "Type mismatch: expected (), got ()"
}

pub fn error_to_string_var_undefined_test_test() {
  let err = VarUndefined("x")
  error_to_string(err) == "Undefined variable: x"
}

pub fn error_to_string_hole_unsolved_test_test() {
  let err = HoleUnsolved(1)
  error_to_string(err) == "Unsolved hole: ?1"
}

pub fn error_to_string_not_a_function_test_test() {
  let err = NotAFunction(VUnit)
  error_to_string(err) == "Not a function: ()"
}

pub fn error_to_string_ctr_undefined_test_test() {
  let err = CtrUndefined("my_ffi")
  error_to_string(err) == "Undefined constructor: my_ffi"
}

pub fn error_to_string_match_missing_test_test() {
  let err = MatchMissing(["x"], ["x"])
  error_to_string(err) == "Missing match cases. Patterns not covered: x. Covered: x"
}

pub fn error_to_string_match_redundant_test_test() {
  let err = MatchRedundant
  error_to_string(err) == "Redundant match case"
}

pub fn error_to_string_step_limit_test_test() {
  let err = StepLimitExceeded(10000)
  error_to_string(err) == "Step limit exceeded (10000 steps)"
}
