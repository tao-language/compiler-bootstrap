// ============================================================================
// CORE STATE - Type Checking State and Error Handling
// ============================================================================
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span}
import core/ast as ast

pub type Permission {
  AllowRead(path: String)
  AllowWrite(path: String)
}

pub type Builtin {
  Builtin(
    impl: fn(List(ast.Value)) -> Option(ast.Value),
    required_permissions: List(Permission),
  )
}

pub type FFI =
  List(#(String, Builtin))

pub type State {
  State(
    ctrs: List(#(String, ast.CtrDef)),
    vars: List(#(String, #(ast.Value, ast.Type))),
    subst: List(#(Int, ast.Value)),
    errors: List(Error),
    warnings: List(Error),
    hole_counter: Int,
    var_counter: Int,
    level: Int,  // Absolute De Bruijn level for HVar indices
    lambda_depth: Int,  // Tracks nesting depth of lambdas for hole generalization
    hole_depths: List(#(Int, Int)),  // Maps hole_id → lambda_depth where created
    step_counter: Int,
    max_steps: Int,
    ffi: FFI,
  )
}

pub type Config {
  Config(
    allow_non_exhaustive: Bool,
    allow_incomplete_patterns: Bool,
    allow_holes: Bool,
    max_steps: Int,
  )
}

pub type Error {
  SyntaxError(span: Span, expected: String, got: String, context: String)
  TypeMismatch(expected: ast.Type, got: ast.Type, expected_span: Span, got_span: Span)
  PatternMismatch(
    pattern: ast.Pattern,
    expected_type: ast.Type,
    pattern_span: Span,
    value_span: Span,
  )
  InfiniteType(hole_id: Int, ty: ast.Type, span1: Span, span2: Span)
  NotAFunction(fun: ast.Term, fun_ty: ast.Value)
  VarUndefined(index: Int, span: Span)
  RcdMissingFields(name: List(String), span: Span)
  CtrUndefined(tag: String, span: Span)
  CtrUnsolvedParam(tag: String, ctr: ast.CtrDef, id: Int, span: Span)
  DotFieldNotFound(name: String, fields: List(#(String, ast.Value)), span: Span)
  DotOnNonCtr(value: ast.Value, name: String, span: Span)
  HoleUnsolved(id: Int, span: Span)
  SpineMismatch(span1: Span, span2: Span)
  ArityMismatch(span1: Span, span2: Span)
  TODO(message: String)
  MatchMissingCase(span: Span, pattern: ast.Pattern)
  MatchRedundantCase(span: Span)
  ComptimePermissionDenied(
    operation: String,
    span: Span,
    required: List(Permission),
  )
  /// Duplicate definition at module level - shadowing not allowed globally
  NameShadow(name: String, first_def: Span, second_def: Span)
}

pub type PHead {
  PHead(tag: String, arity: Int, span: Span)
}

// ============================================================================
// INITIAL STATE
// ============================================================================

pub const initial_state = State(
  ctrs: [],
  vars: [],
  subst: [],
  errors: [],
  warnings: [],
  hole_counter: 0,
  var_counter: 0,
  level: 0,  // Start at level 0 (root)
  lambda_depth: 0,  // Start at depth 0 (no nested lambdas)
  hole_depths: [],  // No holes created yet
  step_counter: 0,
  max_steps: 10000,
  ffi: [],  // FFI is populated by the language layer (Tao)
)

// ============================================================================
// STATE HELPERS
// ============================================================================

pub fn with_err(s: State, err: Error) -> State {
  State(..s, errors: [err, ..s.errors])
}

/// Create a new hole ID and return it with updated state.
pub fn new_hole(s: State) -> #(Int, State) {
  #(s.hole_counter, State(..s, hole_counter: s.hole_counter + 1))
}

/// Create a new hole value (VNeut(HHole(id), [])) with depth tracking for
/// lambda generalization. Returns the hole value and updated state.
pub fn new_hole_value(s: State, lambda_depth: Int) -> #(ast.Value, State) {
  let id = s.hole_counter
  let hole_val = ast.VNeut(ast.HHole(id), [])
  let s = State(
    ..s,
    hole_counter: id + 1,
    hole_depths: [#(id, lambda_depth), ..s.hole_depths],
  )
  #(hole_val, s)
}

/// Create a new hole type (VNeut(HHole(id), [])) without depth tracking.
/// For unification contexts where depth tracking isn't needed.
pub fn new_hole_unify(s: State) -> #(ast.Value, State) {
  let id = s.hole_counter
  let hole_val = ast.VNeut(ast.HHole(id), [])
  #(hole_val, State(..s, hole_counter: id + 1))
}

pub fn new_var(s: State) -> #(Int, State) {
  #(s.var_counter, State(..s, var_counter: s.var_counter + 1))
}

pub fn def_var(
  s: State,
  name: String,
  value: ast.Value,
  typ: ast.Type,
) -> State {
  State(..s, vars: [#(name, #(value, typ)), ..s.vars])
}

pub fn lookup_var(s: State, name: String) -> Result(#(ast.Value, ast.Type), Nil) {
  lookup_var_loop(s.vars, name)
}

fn lookup_var_loop(
  vars: List(#(String, #(ast.Value, ast.Type))),
  name: String,
) -> Result(#(ast.Value, ast.Type), Nil) {
  case vars {
    [] -> Error(Nil)
    [#(n, v), ..rest] -> {
      case n == name {
        True -> Ok(v)
        False -> lookup_var_loop(rest, name)
      }
    }
  }
}

// ============================================================================
// LIST HELPERS
// ============================================================================

pub fn list_get(list: List(a), index: Int) -> Result(a, Nil) {
  list_get_loop(list, index, 0)
}

fn list_get_loop(list: List(a), index: Int, current: Int) -> Result(a, Nil) {
  case list {
    [] -> Error(Nil)
    [x, ..xs] -> {
      case current == index {
        True -> Ok(x)
        False -> list_get_loop(xs, index, current + 1)
      }
    }
  }
}

// No built-in FFI definitions in Core — these are language-specific and belong
// in the language layer (e.g., src/tao/compiler.gleam). Core's `State` accepts
// FFI via the `ffi` field but provides no default implementations.
