/// Core State — Type checking state, FFI, and error handling.
///
/// The `State` type carries all mutable state during type checking
/// and evaluation. It tracks variables, errors, holes, and FFI
/// definitions.
///
/// Errors accumulate as the type checker progresses, allowing
/// recovery after type errors.

import core/ast.{type Value}
import gleam/int
import gleam/list
import gleam/option.{type Option}

// ============================================================================
// FFI
// ============================================================================

/// FFI entry — a builtin function that can be called from Core code.
///
/// The `impl` receives a list of #(value, type) pairs, where the type
/// is the result of type-checking the argument. This enables operator
/// overloading in Phase 5.
pub type FfiEntry {
  FfiEntry(
    fn_name: String,
    impl: fn(List(#(Value, Value))) -> Option(Value),
  )
}

// ============================================================================
// STATE
// ============================================================================

/// Type checking and evaluation state.
///
/// State is threaded through every phase of the compiler. Fields:
///
/// * `vars` — Variable environment (name → #(value, type))
/// * `errors` — Accumulated errors during type checking
/// * `ffi` — FFI builtin definitions available at runtime
/// * `hole_counter` — Next fresh hole ID
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),
    errors: List(Error),
    ffi: List(FfiEntry),
    hole_counter: Int,
  )
}

/// Create a fresh initial state.
pub fn initial_state(ffi: List(FfiEntry)) -> State {
  State(
    vars: [],
    errors: [],
    ffi: ffi,
    hole_counter: 0,
  )
}
// ============================================================================
// STATE HELPERS — Error accumulation
// ============================================================================

/// Add an error to the state.
///
/// The state is returned unchanged — the caller is responsible for
/// using the returned state to continue.
pub fn with_err(state: State, error: Error) -> State {
  State(..state, errors: [error, ..state.errors])
}

/// Continue with a state that has accumulated multiple errors.
///
/// Use this when a function needs to produce several errors but
/// wants to keep going.
pub fn continue_with_errors(state: State, errors: List(Error)) -> State {
  State(..state, errors: list.append(errors, state.errors))
}

// ============================================================================
// STATE HELPERS — Variable environment
// ============================================================================

/// Bind a variable in the state.
///
/// The variable is added to the front of the environment, so the
/// most recently bound variable is found first.
///
/// Returns the updated state.
pub fn def_var(state: State, name: String, value: Value, type_: Value) -> State {
  State(
    ..state,
    vars: [#(name, #(value, type_)), ..state.vars],
  )
}

/// Look up a variable in the state.
///
/// Returns `Error(Nil)` if the variable is not found.
pub fn lookup_var(state: State, name: String) -> Result(#(Value, Value), Nil) {
  lookup_loop(state.vars, name)
}

fn lookup_loop(
  vars: List(#(String, #(Value, Value))),
  name: String,
) -> Result(#(Value, Value), Nil) {
  case vars {
    [] -> Error(Nil)
    [#(n, v), ..rest] -> case n == name {
      True -> Ok(v)
      False -> lookup_loop(rest, name)
    }
  }
}

/// Look up a variable by De Bruijn level.
///
/// `level` is the number of binders to skip from the outermost.
/// Level 0 refers to the most recently bound variable.
pub fn lookup_by_level(state: State, level: Int) -> Result(#(Value, Value), Nil) {
  lookup_by_level_loop(state.vars, level)
}

fn lookup_by_level_loop(
  vars: List(#(String, #(Value, Value))),
  level: Int,
) -> Result(#(Value, Value), Nil) {
  case vars {
    [] -> Error(Nil)
    [#(_, v), ..rest] -> case level {
      0 -> Ok(v)
      _ -> lookup_by_level_loop(rest, level - 1)
    }
  }
}

// ============================================================================
// STATE HELPERS — Holes
// ============================================================================

/// Create a new fresh hole ID.
///
/// Returns the ID and the updated state. Hole IDs are monotonically
/// increasing.
///
/// Positive IDs are type-level holes; negative IDs are term-level holes.
pub fn new_hole(state: State) -> #(Int, State) {
  let id = state.hole_counter
  #(id, State(..state, hole_counter: id + 1))
}

/// Create a fresh hole value (VNeut(HHole(id), [])).
pub fn new_hole_value(state: State) -> #(Value, State) {
  let id = state.hole_counter
  let hole = ast.make_hole_neut(id)
  #(hole, State(..state, hole_counter: id + 1))
}

/// Get the current hole counter value.
pub fn hole_counter(state: State) -> Int {
  state.hole_counter
}
// ============================================================================
// STATE HELPERS — FFI
// ============================================================================

/// Register an FFI entry in the state.
///
/// Returns the updated state with the new FFI entry added.
pub fn with_ffi_entry(state: State, entry: FfiEntry) -> State {
  State(..state, ffi: [entry, ..state.ffi])
}

/// Look up an FFI entry by name.
///
/// Returns `Error(Nil)` if the name is not found.
pub fn lookup_ffi(state: State, name: String) -> Result(FfiEntry, Nil) {
  lookup_ffi_loop(state.ffi, name)
}

fn lookup_ffi_loop(
  ffi: List(FfiEntry),
  name: String,
) -> Result(FfiEntry, Nil) {
  case ffi {
    [] -> Error(Nil)
    [entry, ..rest] -> case entry.fn_name == name {
      True -> Ok(entry)
      False -> lookup_ffi_loop(rest, name)
    }
  }
}
/// Type checking errors.
pub type Error {
  TypeMismatch(expected: Value, got: Value, span: Span)
  VarUndefined(name: String, span: Span)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(fun_type: Value, span: Span)
  CtrUndefined(tag: String, span: Span)
  MatchMissing(patterns: List(String), covered: List(String), span: Span)
  MatchRedundant(span: Span)
  StepLimitExceeded(steps: Int, span: Span)
}

/// Span type for error reporting.
import syntax/span.{type Span}

// ============================================================================
// ERROR HELPERS
// ============================================================================

/// Create a VarUndefined error for a variable at a given De Bruijn level.
/// The name is synthesized as "v@{level}" for debugging.
pub fn undef_var_error(level: Int, span: Span) -> Error {
  VarUndefined("v@" <> int.to_string(level), span)
}

/// Check if the state has any errors.
pub fn has_errors(state: State) -> Bool {
  state.errors != []
}

/// Get all errors from the state (most recent first).
pub fn errors(state: State) -> List(Error) {
  state.errors
}

/// Extract just the variable bindings from the state (without errors).
pub fn get_vars(state: State) -> List(#(String, #(Value, Value))) {
  state.vars
}

/// Format an error as a human-readable string.
pub fn error_to_string(error: Error) -> String {
  case error {
    TypeMismatch(expected, got, _) ->
      "Type mismatch: expected " <> ast.value_to_string(expected)
      <> ", got " <> ast.value_to_string(got)
    VarUndefined(name, _) ->
      "Undefined variable: " <> name
    HoleUnsolved(id, _) ->
      "Unsolved hole: ?" <> int.to_string(id)
    NotAFunction(fun_type, _) ->
      "Not a function: " <> ast.value_to_string(fun_type)
    CtrUndefined(tag, _) ->
      "Undefined constructor: " <> tag
    MatchMissing(patterns, covered, _) ->
      "Missing match cases. Patterns not covered: "
      <> join_list(patterns, ", ")
      <> ". Covered: " <> join_list(covered, ", ")
    MatchRedundant(_) -> "Redundant match case"
    StepLimitExceeded(steps, _) ->
      "Step limit exceeded (" <> int.to_string(steps) <> " steps)"
  }
}

/// Join a list of strings with a separator.
fn join_list(items: List(String), separator: String) -> String {
  case items {
    [] -> ""
    [first, ..rest] -> {
      let rec_join = fn(acc: String, item: String) -> String {
        acc <> separator <> item
      }
      first <> list.fold(rest, "", rec_join)
    }
  }
}
