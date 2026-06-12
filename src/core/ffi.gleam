import core/literals as lit
import core/value.{type Value} as v
import gleam/option.{type Option, None, Some}

/// FFI entry — a builtin function that can be called from Core code.
pub type FFI =
  List(#(String, BuiltIn))

pub type BuiltIn =
  fn(List(Value)) -> Option(Value)

pub const build = [
  #("int_add", int_add),
  #("int_sub", int_sub),
  #("int_mul", int_mul),
]

fn int_add(args: List(Value)) -> Option(Value) {
  case args {
    [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x + y))
    _ -> None
  }
}

fn int_sub(args: List(Value)) -> Option(Value) {
  case args {
    [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x - y))
    _ -> None
  }
}

fn int_mul(args: List(Value)) -> Option(Value) {
  case args {
    [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x * y))
    _ -> None
  }
}
