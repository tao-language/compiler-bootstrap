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
import core/ast.{type AST}
import core/literals.{type Literal, type LiteralType} as lit
import core/utils
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span

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
  RcdT(fields: List(#(String, #(Term, Option(Term)))))
  Call(name: String, args: List(Term))
  Ann(term: Term, type_: Term)
  Lam(param: #(String, Term), body: Term)
  Pi(implicit: Bool, domain: #(String, Term), codomain: Term)
  Fix(name: String, body: Term)
  App(fun: Term, arg: Term)
  TypeDef(type_def: TypeDefinition)
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
  PErr
}

pub type Case {
  Case(pattern: Pattern, guard: Option(#(Term, Pattern)), body: Term)
}

pub type TypeDefinition {
  TypeDefinition(
    params: List(#(String, Term)),
    arg: Term,
    variants: List(#(String, Variant)),
  )
}

pub type Variant {
  Variant(params: List(#(String, Term)), arg: Term, return_type: Term)
}

//
// Helper functions

pub fn bindings(p: Pattern) -> List(String) {
  case p {
    PAny -> []
    PTyp(_) -> []
    PLit(_) -> []
    PLitT(_) -> []
    PAlias(name, p) -> [name, ..bindings(p)]
    PCtr(_, p) -> bindings(p)
    PRcd(fields) -> list.flat_map(fields, fn(kv) { bindings(kv.1) })
    PErr -> []
  }
}

pub fn to_ast(term: Term, names: List(String)) -> AST {
  let s = span.empty("", 0, 0)
  case term {
    Typ(u) -> ast.typ(u, s)
    Hole(id) -> ast.hole(id, s)
    Lit(lit) -> ast.AST(ast.Lit(lit), s)
    LitT(lit_t) -> ast.AST(ast.LitT(lit_t), s)
    Var(index) ->
      case utils.list_at(names, index) {
        Some(name) -> ast.var(name, s)
        None -> ast.var("`undefined " <> int.to_string(index) <> "`", s)
      }
    Ctr(tag, arg) -> ast.AST(ast.Ctr(tag, to_ast(arg, names)), s)
    Rcd(fields) -> todo
    RcdT(fields) -> todo
    Call(name, args) -> todo
    Ann(term, type_) -> todo
    Lam(param, body) -> todo
    Pi(implicit, domain, codomain) -> todo
    Fix(name, body) -> todo
    App(fun, arg) -> todo
    TypeDef(type_def) -> todo
    Match(arg, cases) -> todo
    Err -> todo
  }
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
