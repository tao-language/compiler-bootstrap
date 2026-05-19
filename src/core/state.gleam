/// Core State — Type checking state, FFI, and error handling.
///
/// The `State` type carries all mutable state during type checking
/// and evaluation. It tracks variables, errors, holes, and FFI
/// definitions.
///
/// Errors accumulate as the type checker progresses, allowing
/// recovery after type errors.
import core/ast.{type Value, VTyp}
import core/shift.{shift_value}
import core/utils
import gleam/int
import gleam/list
import gleam/option.{type Option}
import syntax/span.{type Span, Span}

// ============================================================================
// FFI
// ============================================================================

/// FFI entry — a builtin function that can be called from Core code.
///
/// The `impl` receives a list of #(value, type) pairs, where the type
/// is the result of type-checking the argument. This enables operator
/// overloading in Phase 5.
pub type FfiEntry {
  FfiEntry(fn_name: String, impl: fn(List(#(Value, Value))) -> Option(Value))
}

pub type FFI =
  List(FfiEntry)

// ============================================================================
// STATE
// ============================================================================

/// Type checking and evaluation state.
///
/// State is threaded through every phase of the compiler. Fields:
///
/// * `vars`: Variable environment (name → #(value, type))
/// * `subst`: Hole substitutions (hole_id → value)
/// * `errors`: Accumulated errors during type checking
/// * `ffi`: FFI builtin definitions available at runtime
/// * `hole_counter`: Next fresh hole ID
pub type State {
  State(
    vars: List(#(String, Value, Value)),
    subst: Subst,
    errors: List(Error),
    ffi: FFI,
    hole_counter: Int,
  )
}

pub type Subst =
  List(#(Int, Value))

/// Type checking errors.
pub type Error {
  VarUndefined(level: Int, span: Span)
  TypeMismatch(#(Value, Span), #(Value, Span))
  SpineArityMismatch(List(ast.Elim), List(ast.Elim))
  SpineElimMismatch(ast.Elim, ast.Elim)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(fun_type: Value, span: Span)
  CtrUndefined(tag: String, span: Span)
  MatchMissing(patterns: List(String), covered: List(String), span: Span)
  MatchRedundant(span: Span)
  StepLimitExceeded(steps: Int, span: Span)
  CtorArgTypeMismatch(
    tag: String,
    expected_pattern: Value,
    actual_type: Value,
    span: Span,
  )
  CtorNotFound(tag: String, span: Span)
}

pub const new_state = State(
  vars: [],
  subst: [],
  errors: [],
  ffi: [],
  hole_counter: 0,
)

pub fn state_to_env(state: State) -> List(Value) {
  list.map(state.vars, fn(entry) { entry.1 })
}

pub fn env_to_state(env: List(Value), ffi: FFI) -> State {
  let vars =
    list.index_map(env, fn(value, i) {
      let name = ast.value_to_string(ast.vvar(i, []))
      #(name, value, VTyp(i))
    })
  State(..new_state, vars: vars, ffi: ffi)
}

pub fn with_err(state: State, error: Error) -> State {
  with_err_list(state, [error])
}

pub fn with_err_list(state: State, errors: List(Error)) -> State {
  State(..state, errors: list.append(state.errors, errors))
}

pub fn with_subst(state: State, id: Int, value: ast.Value) -> State {
  State(..state, subst: [#(id, value), ..state.subst])
}

/// Restores the variable scope of a state to a previous length,
/// but preserves all hole substitutions, errors, and the hole counter.
pub fn restore_scope(state: State, old_vars_length: Int) -> State {
  let to_drop = list.length(state.vars) - old_vars_length
  State(..state, vars: list.drop(state.vars, to_drop))
}

pub fn vars_shift(state: State, delta: Int) -> State {
  let shifted_vars =
    list.map(state.vars, fn(entry) {
      let #(name, value, type_) = entry
      #(name, shift_value(value, delta), shift_value(type_, delta))
    })
  State(..state, vars: shifted_vars)
}

pub fn vars_push(state: State, var: #(String, Value, Value)) -> State {
  State(..state, vars: [var, ..state.vars])
}

pub fn vars_pop(state: State, num_vars: Int) -> State {
  case num_vars > 0, state.vars {
    True, [_, ..vars] -> vars_pop(State(..state, vars: vars), num_vars - 1)
    _, _ -> state
  }
}

pub fn new_hole(state: State) -> #(Int, State) {
  let id = state.hole_counter
  #(id, State(..state, hole_counter: id + 1))
}
