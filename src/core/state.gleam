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
  ffi: initial_ffis,
)

// ============================================================================
// STATE HELPERS
// ============================================================================

pub fn with_err(s: State, err: Error) -> State {
  State(..s, errors: [err, ..s.errors])
}

pub fn new_hole(s: State) -> #(Int, State) {
  #(s.hole_counter, State(..s, hole_counter: s.hole_counter + 1))
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

// ============================================================================
// BUILTIN FFIS
// ============================================================================

pub fn ffi_add(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a + b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a + b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a +. b)))
    _ -> None
  }
}

pub fn ffi_sub(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a - b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a - b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a -. b)))
    _ -> None
  }
}

pub fn ffi_mul(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a * b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a * b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a *. b)))
    _ -> None
  }
}

pub fn ffi_div(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] if b != 0 -> Some(ast.VLit(ast.I32(a / b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] if b != 0 -> Some(ast.VLit(ast.I64(a / b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] if b != 0.0 -> Some(ast.VLit(ast.F64(a /. b)))
    _ -> None
  }
}

pub fn ffi_eq(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a == b))
    _ -> None
  }
}

pub fn ffi_lt(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a < b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a < b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a <. b))
    _ -> None
  }
}

fn bool_to_value(b: Bool) -> ast.Value {
  case b {
    True -> ast.VCtrValue(ast.VCtr("True", ast.VUnit))
    False -> ast.VCtrValue(ast.VCtr("False", ast.VUnit))
  }
}

pub const initial_ffis: FFI = [
  #("add", Builtin(ffi_add, [])),
  #("sub", Builtin(ffi_sub, [])),
  #("mul", Builtin(ffi_mul, [])),
  #("div", Builtin(ffi_div, [])),
  #("eq", Builtin(ffi_eq, [])),
  #("lt", Builtin(ffi_lt, [])),
]
