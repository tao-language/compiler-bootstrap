import core/literals.{type Literal, type LiteralType} as lit
import core/term.{type Case, type Term}
import gleam/option.{type Option}

// ============================================================================
// VALUES (Semantics level - De Bruijn levels)
// ============================================================================

/// Core values - normalized terms after evaluation.
///
/// Values use De Bruijn levels for variables (relative to their
/// binding site), and De Bruijn indices for bodies.
pub type Value {
  Typ(universe: Int)
  Lit(literal: Literal)
  LitT(literal: LiteralType)
  Ctr(tag: String, arg: Value)
  Rcd(fields: List(#(String, Value)))
  RcdT(fields: List(#(String, #(Value, Option(Value)))))
  Neut(neutral: Neut)
  Lam(env: Env, param: #(String, Value), body: Term)
  Pi(env: Env, implicit: Bool, domain: #(String, Value), codomain: Term)
  Fix(env: Env, name: String, body: Term)
  TypeDef(env: Env, type_def: TypeDefinition)
  Err
}

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, Value)),
    arg: Term,
    variants: List(#(String, Variant)),
  )
}

pub type Variant {
  Variant(params: List(#(String, Value)), arg: Term, return_type: Term)
}

pub type Neut {
  NVar(level: Int)
  NHole(id: Int)
  NApp(fun: Neut, arg: Value)
  NMatch(env: Env, arg: Neut, cases: List(Case))
  NCall(name: String, args: List(Value))
}

pub type Env =
  List(Value)

// Syntax sugar

pub fn var(level: Int) -> Value {
  Neut(NVar(level))
}

pub fn hole(id: Int) -> Value {
  Neut(NHole(id))
}

pub fn app(fun: Neut, arg: Value) -> Value {
  Neut(NApp(fun, arg))
}

pub fn match(env: Env, arg: Neut, cases: List(Case)) -> Value {
  Neut(NMatch(env, arg, cases))
}

pub fn call(name: String, args: List(Value)) -> Value {
  Neut(NCall(name, args))
}

pub fn int(value: Int) -> Value {
  Lit(lit.Int(value))
}

pub fn float(value: Float) -> Value {
  Lit(lit.Float(value))
}

pub const int_t = LitT(lit.IntT)

pub const float_t = LitT(lit.FloatT)

pub const i8 = LitT(lit.I8)

pub const i16 = LitT(lit.I16)

pub const i32 = LitT(lit.I32)

pub const i64 = LitT(lit.I64)

pub const u8 = LitT(lit.U8)

pub const u16 = LitT(lit.U16)

pub const u32 = LitT(lit.U32)

pub const u64 = LitT(lit.U64)

pub const f32 = LitT(lit.F32)

pub const f64 = LitT(lit.F64)

pub fn ctr(tag: String, args: List(#(String, Value))) -> Value {
  Ctr(tag, Rcd(args))
}
