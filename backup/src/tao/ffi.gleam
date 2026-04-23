// ============================================================================
// TAO BUILTIN FFIS
// Language-specific FFI operations defined in Tao, not in Core.
// ============================================================================
import core/ast as ast
import core/state as state
import gleam/option.{type Option, None, Some}
import tao/language_config as lang_config

/// All Tao builtin FFI operations.
/// Constructor names come from language_config to avoid hardcoding.
pub fn tao_ffis() -> state.FFI {
  let cfg = lang_config.default_config()
  let bool_t = lang_config.bool_type_as_core(cfg)
  let truth_ctor = cfg.truth_constructor
  let false_ctor = cfg.false_constructor
  [
    #("add", state.Builtin(
      impl: ffi_add,
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: ast.VLitT(ast.ILitT),
      required_permissions: [],
    )),
    #("sub", state.Builtin(
      impl: ffi_sub,
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: ast.VLitT(ast.ILitT),
      required_permissions: [],
    )),
    #("mul", state.Builtin(
      impl: ffi_mul,
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: ast.VLitT(ast.ILitT),
      required_permissions: [],
    )),
    #("div", state.Builtin(
      impl: ffi_div,
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: ast.VLitT(ast.ILitT),
      required_permissions: [],
    )),
    #("eq", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_eq, float_op_eq, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
    #("neq", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_neq, float_op_neq, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
    #("lt", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_lt, float_op_lt, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
    #("gt", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_gt, float_op_gt, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
    #("lte", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_lte, float_op_lte, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
    #("gte", state.Builtin(
      impl: fn(args) { dispatch_cmp(args, int_op_gte, float_op_gte, truth_ctor, false_ctor) },
      arg_types: [ast.VLitT(ast.ILitT), ast.VLitT(ast.ILitT)],
      ret_type: bool_t,
      required_permissions: [],
    )),
  ]
}

// ============================================================================
// GENERIC DISPATCHERS - Binary operations on numeric literals
// ============================================================================

/// Dispatch binary integer arithmetic to matching literal pairs.
fn dispatch_arith(
  args: List(ast.Value),
  int_op: fn(Int, Int) -> Int,
  float_op: fn(Float, Float) -> Float,
) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(int_op(a, b))))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(int_op(a, b))))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(float_op(a, b))))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(ast.VLit(ast.IntLit(int_op(a, b))))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(ast.VLit(ast.FloatLit(float_op(a, b))))
    _ -> None
  }
}

/// Dispatch binary comparison to matching literal pairs.
/// Always returns a boolean constructor value (not a numeric literal).
fn dispatch_cmp(
  args: List(ast.Value),
  int_cmp: fn(Int, Int) -> Bool,
  float_cmp: fn(Float, Float) -> Bool,
  truth_ctor: String,
  false_ctor: String,
) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value_with_constructors(int_cmp(a, b), truth_ctor, false_ctor))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value_with_constructors(int_cmp(a, b), truth_ctor, false_ctor))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value_with_constructors(float_cmp(a, b), truth_ctor, false_ctor))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value_with_constructors(int_cmp(a, b), truth_ctor, false_ctor))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value_with_constructors(float_cmp(a, b), truth_ctor, false_ctor))
    _ -> None
  }
}

/// Dispatch division with zero-check to matching literal pairs.
fn dispatch_div(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> case b != 0 {
      True -> Some(ast.VLit(ast.I32(a / b)))
      False -> None
    }
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> case b != 0 {
      True -> Some(ast.VLit(ast.I64(a / b)))
      False -> None
    }
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> case b != 0.0 {
      True -> Some(ast.VLit(ast.F64(a /. b)))
      False -> None
    }
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> case b != 0 {
      True -> Some(ast.VLit(ast.IntLit(a / b)))
      False -> None
    }
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> case b != 0.0 {
      True -> Some(ast.VLit(ast.FloatLit(a /. b)))
      False -> None
    }
    _ -> None
  }
}

// ============================================================================
// INTERNAL FFI IMPLMENTATIONS
// ============================================================================

/// Public entry point for addition.
pub fn ffi_add(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_add, float_op_add)
}

/// Public entry point for subtraction.
pub fn ffi_sub(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_sub, float_op_sub)
}

/// Public entry point for multiplication.
pub fn ffi_mul(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_mul, float_op_mul)
}

/// Public entry point for division.
pub fn ffi_div(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_div(args)
}

// ============================================================================
// PUBLIC FFI ENTRY POINTS (for test access)
// ============================================================================

/// Public entry point for equality comparison.
pub fn ffi_eq(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_eq, float_op_eq, cfg.truth_constructor, cfg.false_constructor)
}

/// Public entry point for not-equal comparison.
pub fn ffi_neq(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_neq, float_op_neq, cfg.truth_constructor, cfg.false_constructor)
}

/// Public entry point for less-than comparison.
pub fn ffi_lt(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_lt, float_op_lt, cfg.truth_constructor, cfg.false_constructor)
}

/// Public entry point for greater-than comparison.
pub fn ffi_gt(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_gt, float_op_gt, cfg.truth_constructor, cfg.false_constructor)
}

/// Public entry point for less-than-or-equal comparison.
pub fn ffi_lte(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_lte, float_op_lte, cfg.truth_constructor, cfg.false_constructor)
}

/// Public entry point for greater-than-or-equal comparison.
pub fn ffi_gte(args: List(ast.Value)) -> Option(ast.Value) {
  let cfg = lang_config.default_config()
  dispatch_cmp(args, int_op_gte, float_op_gte, cfg.truth_constructor, cfg.false_constructor)
}

// ============================================================================
// COMPARISON OPERATORS
// ============================================================================

fn int_op_eq(a: Int, b: Int) -> Bool { a == b }
fn int_op_neq(a: Int, b: Int) -> Bool { a != b }
fn int_op_lt(a: Int, b: Int) -> Bool { a < b }
fn int_op_gt(a: Int, b: Int) -> Bool { a > b }
fn int_op_lte(a: Int, b: Int) -> Bool { a <= b }
fn int_op_gte(a: Int, b: Int) -> Bool { a >= b }

fn float_op_eq(a: Float, b: Float) -> Bool { a == b }
fn float_op_neq(a: Float, b: Float) -> Bool { a != b }
fn float_op_lt(a: Float, b: Float) -> Bool { a <. b }
fn float_op_gt(a: Float, b: Float) -> Bool { a >. b }
fn float_op_lte(a: Float, b: Float) -> Bool { a <=. b }
fn float_op_gte(a: Float, b: Float) -> Bool { a >=. b }

// ============================================================================
// ARITHMETIC OPERATORS
// ============================================================================

fn int_op_add(a: Int, b: Int) -> Int { a + b }
fn int_op_sub(a: Int, b: Int) -> Int { a - b }
fn int_op_mul(a: Int, b: Int) -> Int { a * b }

fn float_op_add(a: Float, b: Float) -> Float { a +. b }
fn float_op_sub(a: Float, b: Float) -> Float { a -. b }
fn float_op_mul(a: Float, b: Float) -> Float { a *. b }

// ============================================================================
// HELPERS
// ============================================================================

/// Convert boolean to a value using the given truth/false constructor names.
/// This makes the FFI language-agnostic — the constructor names are passed as parameters.
fn bool_to_value_with_constructors(b: Bool, truth_ctor: String, false_ctor: String) -> ast.Value {
  case b {
    True -> ast.VCtrValue(ast.VCtr(truth_ctor, ast.VUnit))
    False -> ast.VCtrValue(ast.VCtr(false_ctor, ast.VUnit))
  }
}
