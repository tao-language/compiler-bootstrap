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
pub type FFI =
  List(#(String, fn(List(#(Value, Value))) -> Option(Value)))

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

pub fn new_hole(state: State) -> #(Int, State) {
  let id = state.hole_counter
  #(id, State(..state, hole_counter: id + 1))
}

pub fn vars_shift(state: State, delta: Int) -> State {
  State(
    ..state,
    vars: list.map(state.vars, fn(var) {
      let #(name, value, type_val) = var
      #(name, shift_value(value, delta), shift_value(type_val, delta))
    }),
  )
}
