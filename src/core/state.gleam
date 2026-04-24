// ============================================================================
// CORE STATE - Type checking and evaluation state
// ============================================================================
/// State management for type checking and evaluation.

import core/ast.{type Type, type Value}
import gleam/list
import gleam/int

// ============================================================================
// FFI ENTRY
// ============================================================================

/// FFI builtin definitions
pub type FfiEntry {
  FfiEntry(
    name: String,
    typ: Type,
    args: List(Type),
    impl: fn(List(Value)) -> Value,
  )
}

// ============================================================================
// TYPE CHECKING STATE
// ============================================================================

/// Hole ID for type inference
type HoleId = Int

/// Type checking environment
pub type Env {
  Env(
    bindings: List(#(String, Type)),
    ffi: List(FfiEntry),
  )
}

/// Type checking errors
pub type TypeError {
  TypeError(
    message: String,
    span: String,
  )
}

/// Type checking state
pub type State {
  State(
    env: Env,
    errors: List(TypeError),
    hole_bindings: List(#(HoleId, Type)),
  )
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Create a new empty state with the given environment
pub fn new_state(env: Env) -> State {
  State(
    env: env,
    errors: [],
    hole_bindings: [],
  )
}

/// Push a binding into the environment
pub fn push_binding(state: State, name: String, typ: Type) -> State {
  State(
    ..state,
    env: Env(
      bindings: [ #(name, typ), ..state.env.bindings ],
      ffi: state.env.ffi,
    ),
  )
}

/// Lookup a variable in the environment
pub fn lookup_env(state: State, name: String) -> Result(Type, TypeError) {
  case list.find(state.env.bindings, fn(b) { b.0 == name }) {
    Ok(#(_, typ)) -> Ok(typ)
    Error(_) -> Error(TypeError(message: "Unknown variable: " <> name, span: ""))
  }
}

/// Add an error to the state
pub fn add_error(state: State, error: TypeError) -> State {
  State(..state, errors: [error, ..state.errors])
}

/// Lookup FFI entry by name
pub fn lookup_ffi(state: State, name: String) -> Result(FfiEntry, TypeError) {
  case list.find(state.env.ffi, fn(ffi) { ffi.name == name }) {
    Ok(ffi) -> Ok(ffi)
    Error(_) -> Error(TypeError(message: "Unknown FFI: " <> name, span: ""))
  }
}

/// Lookup a hole ID in the hole bindings
pub fn lookup_hole(state: State, id: HoleId) -> Result(Type, TypeError) {
  case list.find(state.hole_bindings, fn(h) { h.0 == id }) {
    Ok(#(_, typ)) -> Ok(typ)
    Error(_) -> Error(TypeError(message: "Unknown hole: " <> int.to_string(id), span: ""))
  }
}

/// Bind a hole to a type
pub fn bind_hole(state: State, id: HoleId, typ: Type) -> State {
  State(..state, hole_bindings: [ #(id, typ), ..state.hole_bindings ])
}
