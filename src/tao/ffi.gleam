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

pub fn ffi_add(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a + b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a + b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a +. b)))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(ast.VLit(ast.IntLit(a + b)))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(ast.VLit(ast.FloatLit(a +. b)))
    _ -> None
  }
}

pub fn ffi_sub(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a - b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a - b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a -. b)))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(ast.VLit(ast.IntLit(a - b)))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(ast.VLit(ast.FloatLit(a -. b)))
    _ -> None
  }
}

pub fn ffi_mul(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(ast.VLit(ast.I32(a * b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(ast.VLit(ast.I64(a * b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(ast.VLit(ast.F64(a *. b)))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(ast.VLit(ast.IntLit(a * b)))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(ast.VLit(ast.FloatLit(a *. b)))
    _ -> None
  }
}

pub fn ffi_div(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] if b != 0 -> Some(ast.VLit(ast.I32(a / b)))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] if b != 0 -> Some(ast.VLit(ast.I64(a / b)))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] if b != 0.0 -> Some(ast.VLit(ast.F64(a /. b)))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] if b != 0 -> Some(ast.VLit(ast.IntLit(a / b)))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] if b != 0.0 -> Some(ast.VLit(ast.FloatLit(a /. b)))
    _ -> None
  }
}

pub fn ffi_eq(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(a == b))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(a == b))
    _ -> None
  }
}

pub fn ffi_lt(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a < b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a < b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a <. b))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(a < b))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(a <. b))
    _ -> None
  }
}

pub fn ffi_neq(args: List(ast.Value)) -> Option(ast.Value) {
  case ffi_eq(args) {
    Some(ast.VCtrValue(ast.VCtr("True", _))) -> Some(bool_to_value(False))
    Some(ast.VCtrValue(ast.VCtr("False", _))) -> Some(bool_to_value(True))
    _ -> None
  }
}

pub fn ffi_gt(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a > b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a > b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a >. b))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(a > b))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(a >. b))
    _ -> None
  }
}

pub fn ffi_lte(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a <= b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a <= b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a <=. b))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(a <= b))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(a <=. b))
    _ -> None
  }
}

pub fn ffi_gte(args: List(ast.Value)) -> Option(ast.Value) {
  case args {
    [ast.VLit(ast.I32(a)), ast.VLit(ast.I32(b))] -> Some(bool_to_value(a >= b))
    [ast.VLit(ast.I64(a)), ast.VLit(ast.I64(b))] -> Some(bool_to_value(a >= b))
    [ast.VLit(ast.F64(a)), ast.VLit(ast.F64(b))] -> Some(bool_to_value(a >=. b))
    [ast.VLit(ast.IntLit(a)), ast.VLit(ast.IntLit(b))] -> Some(bool_to_value(a >= b))
    [ast.VLit(ast.FloatLit(a)), ast.VLit(ast.FloatLit(b))] -> Some(bool_to_value(a >=. b))
    _ -> None
  }
}

fn bool_to_value(b: Bool) -> ast.Value {
  case b {
    True -> ast.VCtrValue(ast.VCtr("True", ast.VUnit))
    False -> ast.VCtrValue(ast.VCtr("False", ast.VUnit))
  }
}
