/// A literal value: an integer or a float.
pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

/// A literal *type*. `%Int`/`%Float` are the inferred literal types;
/// the rest are fixed-width types used for FFI and annotations.
pub type LiteralType {
  IntT
  FloatT
  I8
  I16
  I32
  I64
  U8
  U16
  U32
  U64
  F16
  F32
  F64
}

/// Whether the literal type is one of the integer types.
pub fn is_int_type(lit: LiteralType) -> Bool {
  case lit {
    IntT | I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64 -> True
    _ -> False
  }
}

/// Whether the literal type is one of the float types.
pub fn is_float_type(lit: LiteralType) -> Bool {
  case lit {
    FloatT | F16 | F32 | F64 -> True
    _ -> False
  }
}
