// ============================================================================
// TAO BUILTIN FFIS
// Language-specific FFI operations defined in Tao, not in Core.
// ============================================================================
import core/ast as ast
import core/state as state
import gleam/option.{type Option, None, Some}

/// All Tao builtin FFI operations.
pub fn tao_ffis() -> state.FFI {
  [
    #("add", state.Builtin(ffi_add, [])),
    #("sub", state.Builtin(ffi_sub, [])),
    #("mul", state.Builtin(ffi_mul, [])),
    #("div", state.Builtin(ffi_div, [])),
    #("eq", state.Builtin(ffi_eq, [])),
    #("neq", state.Builtin(ffi_neq, [])),
    #("lt", state.Builtin(ffi_lt, [])),
    #("gt", state.Builtin(ffi_gt, [])),
    #("lte", state.Builtin(ffi_lte, [])),
    #("gte", state.Builtin(ffi_gte, [])),
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
fn dispatch_cmp(
  args: List(ast.Value),
  int_cmp: fn(Int, Int) -> Bool,
  float_cmp: fn(Float, Float) -> Bool,
) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(int_cmp(a, b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(int_cmp(a, b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(float_cmp(a, b)))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(int_cmp(a, b)))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(float_cmp(a, b)))
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
// PUBLIC FFI ENTRY POINTS
// ============================================================================

pub fn ffi_add(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_add, float_op_add)
}

pub fn ffi_sub(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_sub, float_op_sub)
}

pub fn ffi_mul(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_arith(args, int_op_mul, float_op_mul)
}

pub fn ffi_div(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_div(args)
}

pub fn ffi_eq(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_eq, float_op_eq)
}

pub fn ffi_neq(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_neq, float_op_neq)
}

pub fn ffi_lt(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_lt, float_op_lt)
}

pub fn ffi_gt(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_gt, float_op_gt)
}

pub fn ffi_lte(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_lte, float_op_lte)
}

pub fn ffi_gte(args: List(ast.Value)) -> Option(ast.Value) {
  dispatch_cmp(args, int_op_gte, float_op_gte)
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

fn bool_to_value(b: Bool) -> ast.Value {
  case b {
    True -> ast.VCtrValue(ast.VCtr("True", ast.VUnit))
    False -> ast.VCtrValue(ast.VCtr("False", ast.VUnit))
  }
}
