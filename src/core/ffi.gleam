import core/literals as lit
import core/value.{type Value} as v
import gleam/option.{type Option, None, Some}

/// FFI entry — a builtin function that can be called from Core code.
pub type FFI =
  List(#(String, BuiltIn))

pub type BuiltIn =
  fn(Value) -> Option(Value)

pub const build = [
  #("int_add", int_add),
  #("int_sub", int_sub),
  #("int_mul", int_mul),
  #("float_add", float_add),
  #("float_sub", float_sub),
  #("float_mul", float_mul),
]

fn int_add(arg: Value) -> Option(Value) {
  int_binop(fn(x, y) { x + y }, arg)
}

fn int_sub(arg: Value) -> Option(Value) {
  int_binop(fn(x, y) { x - y }, arg)
}

fn int_mul(arg: Value) -> Option(Value) {
  int_binop(fn(x, y) { x * y }, arg)
}

fn float_add(arg: Value) -> Option(Value) {
  float_binop(fn(x, y) { x +. y }, arg)
}

fn float_sub(arg: Value) -> Option(Value) {
  float_binop(fn(x, y) { x -. y }, arg)
}

fn float_mul(arg: Value) -> Option(Value) {
  float_binop(fn(x, y) { x *. y }, arg)
}

fn int_binop(f: fn(Int, Int) -> Int, arg: Value) -> Option(Value) {
  case arg {
    v.Rcd([#(_, #(v.Lit(lit.Int(x)), _)), #(_, #(v.Lit(lit.Int(y)), _))], None) ->
      Some(v.int(f(x, y)))
    _ -> None
  }
}

fn float_binop(f: fn(Float, Float) -> Float, arg: Value) -> Option(Value) {
  case arg {
    v.Rcd(
      [#(_, #(v.Lit(lit.Float(x)), _)), #(_, #(v.Lit(lit.Float(y)), _))],
      None,
    ) -> Some(v.float(f(x, y)))
    _ -> None
  }
}
