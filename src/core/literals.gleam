pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

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

pub fn is_int_type(lit: LiteralType) -> Bool {
  case lit {
    IntT | I8 | I16 | I32 | I64 | U8 | U16 | U32 | U64 -> True
    _ -> False
  }
}

pub fn is_float_type(lit: LiteralType) -> Bool {
  case lit {
    FloatT | F16 | F32 | F64 -> True
    _ -> False
  }
}
