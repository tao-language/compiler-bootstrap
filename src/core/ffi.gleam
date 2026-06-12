import core/value.{type Value}
import gleam/option.{type Option}

/// FFI entry — a builtin function that can be called from Core code.
pub type FFI =
  List(#(String, BuiltIn))

pub type BuiltIn =
  fn(List(Value)) -> Option(Value)
