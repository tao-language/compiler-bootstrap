/// Core Abstract Syntax Tree
///
/// The core language is language-agnostic. It defines the fundamental
/// terms and values that make up the compiler's internal representation.
///
/// Terms use De Bruijn **indices** for variables. Values use De Bruijn
/// **levels** for runtime representation.
///
/// De Bruijn **indices** (Term `Var(n)`): relative to binders. `Var(0)` is
/// the innermost binder, `Var(1)` is the next one out, etc.
///
/// De Bruijn **levels** (Value `HVar(n)`): absolute positions in the
/// environment (`state.vars`). Level 0 is the most-recently-pushed entry
/// (innermost binder), level 1 is the next, etc.
///
/// Because `state.vars` is ordered innermost-first (see `state.gleam`),
/// levels and indices use the **same** counting convention:
///   level 0 = index 0 = innermost binder
///   level 1 = index 1 = next binder out
///   ...
/// This means quoting a level to an index is the identity conversion.
import core/literals.{type Literal, type LiteralType} as lit
import gleam/option.{type Option}

// ============================================================================
// TERMS (Syntax level - De Bruijn indices)
// ============================================================================

/// Core terms. The AST for type checking and evaluation.
///
/// Terms use De Bruijn indices: Var(0) refers to the innermost
/// enclosing binder, Var(1) to the one before that, etc.
pub type Term {
  Typ(universe: Int)
  Hole(id: Int)
  Lit(value: Literal)
  LitT(typ: LiteralType)
  Var(index: Int)
  Ctr(tag: String, arg: Term)
  Rcd(fields: List(#(String, Term)))
  RcdT(fields: List(#(String, Term, Option(Term))))
  Call(name: String, args: List(Term))
  Ann(term: Term, type_: Term)
  Lam(implicit: Bool, param: #(String, Term), body: Term)
  Pi(implicit: Bool, domain: #(String, Term), codomain: Term)
  Fix(name: String, body: Term)
  App(fun: Term, arg: Term)
  TypeDef(
    params: List(#(String, Term)),
    variants: List(#(String, #(List(#(String, Term)), Term, Term))),
  )
  Match(arg: Term, cases: List(Case))
  Err
}

pub type Pattern {
  PAny
  PTyp(universe: Int)
  PLit(value: Literal)
  PLitT(lit_type: LiteralType)
  PAlias(name: String, pattern: Pattern)
  PCtr(tag: String, pattern: Pattern)
  PRcd(fields: List(#(String, Pattern)))
  PError
}

pub type Case {
  Case(pattern: Pattern, guard: Option(#(Term, Pattern)), body: Term)
}

// Syntax sugar

pub fn int(value: Int) -> Term {
  Lit(lit.Int(value))
}

pub fn float(value: Float) -> Term {
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

pub fn ctr(tag: String, args: List(#(String, Term))) -> Term {
  Ctr(tag, Rcd(args))
}

/// Syntax sugar for `_@name`.
pub fn pvar(name: String) -> Pattern {
  PAlias(name, PAny)
}

pub fn pint(value: Int) -> Pattern {
  PLit(lit.Int(value))
}

pub fn pfloat(value: Float) -> Pattern {
  PLit(lit.Float(value))
}
