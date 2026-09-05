import core/literals.{type Literal, type LiteralType} as lit
import core/term.{type Case, type Term}
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}

// ============================================================================
// VALUES (Semantics level - De Bruijn levels)
// ============================================================================

/// Core values - normalized terms after evaluation.
///
/// `NVar(level)` refers to an environment entry by *de Bruijn level*:
/// level `n` is the `n`th entry from the outermost end (the number of
/// entries the environment had when the entry was pushed). Levels are
/// unchanged by pushing or popping innermost entries, so captured
/// environments (`Pi`/`Lam`/`For`/`Fix` bodies, `NMatch`) stay valid
/// across inference. Quoting converts a level to a de Bruijn *index*
/// with `index = env_size - level - 1` (see `quote`).
///
/// Bodies are Terms, which use plain de Bruijn *indices* (0 = innermost).
pub type Value {
  Typ(universe: Int)
  Lit(literal: Literal)
  LitT(literal: LiteralType)
  Ctr(tag: String, arg: Value)
  Rcd(fields: List(#(String, #(Value, Option(Value)))), tail: Option(Value))
  Neut(neutral: Neut)
  For(env: Env, param: #(String, Type), body: Term)
  Lam(env: Env, param: #(String, Type), body: Term)
  Pi(env: Env, domain: #(String, Type), codomain: Term)
  Fix(env: Env, name: String, body: Term)
  TypeDef(env: Env, type_def: TypeDefinition)
  Err
}

pub type Type =
  Value

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
  NHole(env: Env, id: Option(Int))
  NApp(fun: Neut, arg: Value)
  NMatch(env: Env, arg: Neut, cases: List(Case))
  NCall(name: String, ret: Type, arg: Value)
}

/// Values environment, innermost (newest) first.
pub type Env =
  List(Value)

// Helper functions

/// Push `num_vars` fresh neutral entries in one go (e.g. for a pattern
/// binding several variables). The new entries take the next levels
/// (`length(env)` upwards); existing entries' levels are untouched.
pub fn env_push(env: Env, num_vars: Int) -> Env {
  int.range(
    from: list.length(env),
    to: list.length(env) + num_vars,
    with: [],
    run: list.prepend,
  )
  |> list.map(var)
  |> list.append(env)
}

pub fn is_concrete(value: Value) -> Bool {
  case value {
    Neut(_) -> False
    Ctr(_, arg) -> is_concrete(arg)
    Rcd(fields, tail) ->
      list.all(fields, is_concrete_field) && is_concrete_opt(tail)
    _ -> True
  }
}

fn is_concrete_field(field: #(String, #(Value, Option(Value)))) -> Bool {
  let #(_, #(value, opt_default)) = field
  is_concrete(value) && is_concrete_opt(opt_default)
}

fn is_concrete_opt(opt_value: Option(Value)) -> Bool {
  case opt_value {
    Some(value) -> is_concrete(value)
    None -> True
  }
}

// Syntax sugar

/// A neutral variable for the entry at the given de Bruijn level (counted
/// from the outermost end; see the `Value` docs).
pub fn var(level: Int) -> Value {
  Neut(NVar(level))
}

pub fn hole(env: Env, id: Int) -> Value {
  hole_open(env, Some(id))
}

/// A neutral hole that captured `env` at creation, so neutral variables
/// in its eventual solution are addressable when it is re-evaluated.
pub fn hole_open(env: Env, id: Option(Int)) -> Value {
  Neut(NHole(env, id))
}

/// A neutral application: the function head is not (yet) a lambda.
pub fn app(fun: Neut, arg: Value) -> Value {
  Neut(NApp(fun, arg))
}

/// A neutral match: the scrutinee is not (yet) a concrete value.
pub fn match(env: Env, arg: Neut, cases: List(Case)) -> Value {
  Neut(NMatch(env, arg, cases))
}

/// A deferred call to a name with no FFI definition (an `extern`), kept
/// neutral so it can be quoted back to source. `ret` is its return type,
/// used for type checking only.
pub fn call(name: String, ret: Type, arg: Value) -> Value {
  Neut(NCall(name, ret, arg))
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

pub const f16 = LitT(lit.F16)

pub const f32 = LitT(lit.F32)

pub const f64 = LitT(lit.F64)

/// A closed record value (no default values on any field).
pub fn rcd(fields: List(#(String, Value))) -> Value {
  rcd_open(fields, None)
}

pub fn rcd_open(fields: List(#(String, Value)), tail: Option(Value)) -> Value {
  let fields =
    list.map(fields, fn(field) {
      let #(name, value) = field
      #(name, #(value, None))
    })
  Rcd(fields, tail)
}

/// A constructor value: a record of (possibly positional) arguments.
pub fn ctr(tag: String, args: List(#(String, Value))) -> Value {
  Ctr(tag, rcd(args))
}
