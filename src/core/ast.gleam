/// Core Abstract Syntax Tree
///
/// The core language is language-agnostic. It defines the fundamental
/// terms and values that make up the compiler's internal representation.
///
/// Terms use De Bruijn indices for variables. Values use De Bruijn
/// levels for runtime representation.

import gleam/int
import gleam/list
import gleam/float
import syntax/span.{type Span}

// ============================================================================
// LITERALS
// ============================================================================

/// Literal values in the core language.
///
/// Simplified: single Int and Float types. Extended in Phase 5 to
/// support I32/I64/U32/U64/F32/F64 with literal type polymorphism.
pub type Literal {
  Int(value: Int)
  Float(value: Float)
}

/// Literal type annotations for type checking.
///
/// Simplified: single I32T and FLitT. Extended in Phase 5 to support
/// the full set of integer and float literal types.
pub type LiteralType {
  IntT
  FloatT
}

// ============================================================================
// TERMS (Syntax level — De Bruijn indices)
// ============================================================================

/// Core terms. The AST for type checking and evaluation.
///
/// Terms use De Bruijn indices: Var(0) refers to the innermost
/// enclosing binder, Var(1) to the one before that, etc.
pub type Term {
  Var(index: Int, span: Span)
  Hole(id: Int, span: Span)
  Lam(param: #(String, Term), body: Term, span: Span)
  App(fun: Term, arg: Term, span: Span)
  Pi(domain: Term, codomain: Term, span: Span)
  Lit(value: Literal, span: Span)
  Ctr(tag: String, arg: Term, span: Span)
  Match(arg: Term, cases: List(Case), span: Span)
  Let(name: String, value: Term, body: Term, span: Span)
  Ann(term: Term, type_: Term, span: Span)
  Unit(span: Span)
  Typ(span: Span)
  Err(message: String, span: Span)
}

/// A pattern in a match case.
pub type Pattern {
  PAny(span: Span)
  PVar(name: String, span: Span)
  PCtr(tag: String, pattern: Pattern, span: Span)
  PUnit(span: Span)
  PLit(value: Literal, span: Span)
}

/// A case in a match expression.
pub type Case {
  Case(pattern: Pattern, body: Term, span: Span)
}

// ============================================================================
// VALUES (Semantics level — De Bruijn levels)
// ============================================================================

/// Neutral term head — the start of a neutral spine.
pub type Head {
  HVar(level: Int)
  HHole(id: Int)
}

/// Elimination form applied to a neutral term.
pub type Elim {
  EApp(arg: Value)
}

/// Core values — normalized terms after evaluation.
///
/// Values use De Bruijn levels for variables (relative to their
/// binding site), and De Bruijn indices for bodies.
pub type Value {
  VNeut(head: Head, spine: List(Elim))
  VLam(param: #(String, Term), body: Term)
  VPi(domain: Value, codomain: Value)
  VLit(value: Literal)
  VCtr(tag: String, arg: Value)
  VUnit
  VErr
}

// ============================================================================
// HELPERS
// ============================================================================

/// Create a neutral value with no spine.
pub fn make_neut(head: Head) -> Value {
  VNeut(head, [])
}

/// Create a neutral value from a hole ID.
pub fn make_hole_neut(id: Int) -> Value {
  VNeut(HHole(id), [])
}

/// Create a neutral value from a De Bruijn level.
pub fn make_var_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

/// Create an error term (avoids conflict with Gleam's built-in Err).
pub fn error_term(message: String, span: Span) -> Term {
  Err(message, span)
}

/// Extract the span from a term.
pub fn get_span(term: Term) -> Span {
  case term {
    Var(_, span) -> span
    Hole(_, span) -> span
    Lam(_, _, span) -> span
    App(_, _, span) -> span
    Pi(_, _, span) -> span
    Lit(_, span) -> span
    Ctr(_, _, span) -> span
    Match(_, _, span) -> span
    Let(_, _, _, span) -> span
    Ann(_, _, span) -> span
    Unit(span) -> span
    Typ(span) -> span
    Err(_, span) -> span
  }
}

// ============================================================================
// TERM SHIFTING (De Bruijn index manipulation)
// ============================================================================

/// Shift all De Bruijn indices in a term by `shift`.
///
/// Positive shift opens up scopes (e.g., when inserting a new binder).
/// Negative shift closes scopes (e.g., when leaving a binder).
///
/// Only shifts indices >= `from` — this allows selective shifting
/// (e.g., shifting only free indices, not bound ones).
pub fn shift_term(term: Term, shift: Int) -> Term {
  shift_term_from(term, shift, 0)
}

fn shift_term_from(term: Term, shift: Int, from: Int) -> Term {
  case term {
    Var(i, span) ->
      case i >= from {
        True -> Var(i + shift, span)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(#(name, param), body, span) ->
      Lam(#(name, shift_term_from(param, shift, from)),
          shift_term_from(body, shift, from + 1),
          span)
    App(fun, arg, span) ->
      App(shift_term_from(fun, shift, from),
          shift_term_from(arg, shift, from),
          span)
    Pi(domain, codomain, span) ->
      Pi(shift_term_from(domain, shift, from),
         shift_term_from(codomain, shift, from),
         span)
    Lit(value, span) -> Lit(value, span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term_from(arg, shift, from), span)
    Match(arg, cases, span) ->
      Match(shift_term_from(arg, shift, from),
            list.map(cases, fn(c) { shift_case(c, shift, from) }),
            span)
    Let(name, value, body, span) ->
      Let(name,
          shift_term_from(value, shift, from),
          shift_term_from(body, shift, from + 1),
          span)
    Ann(term, type_, span) ->
      Ann(shift_term_from(term, shift, from),
          shift_term_from(type_, shift, from),
          span)
    Unit(span) -> Unit(span)
    Typ(span) -> Typ(span)
    Err(msg, span) -> Err(msg, span)
  }
}

fn shift_case(case_: Case, shift: Int, from: Int) -> Case {
  Case(case_.pattern, shift_term_from(case_.body, shift, from), case_.span)
}

// ============================================================================
// STRING REPRESENTATION (Debug)
// ============================================================================

/// Format a term for debugging / display.
///
/// This is NOT a formatter — it's a simple string representation for
/// debugging. The actual formatter lives in the syntax layer.
pub fn term_to_string(term: Term) -> String {
  case term {
    Var(i, _) -> "#" <> int.to_string(i)
    Hole(id, _) -> "?" <> int.to_string(id)
    Lam(#(name, _), body, _) ->
      "λ" <> name <> "." <> term_to_string(body)
    App(fun, arg, _) ->
      "(" <> term_to_string(fun) <> " " <> term_to_string(arg) <> ")"
    Pi(domain, codomain, _) ->
      "Π" <> term_to_string(domain) <> "." <> term_to_string(codomain)
    Lit(Int(value), _) -> int.to_string(value)
    Lit(Float(value), _) -> float.to_string(value)
    Ctr(tag, arg, _) -> tag <> "(" <> term_to_string(arg) <> ")"
    Match(arg, cases, _) ->
      "match " <> term_to_string(arg) <> " {"
      <> cases_to_string(cases)
      <> "}"
    Let(name, value, body, _) ->
      "let " <> name <> " = " <> term_to_string(value) <> "; " <> term_to_string(body)
    Ann(term, type_, _) ->
      term_to_string(term) <> ": " <> term_to_string(type_)
    Unit(_) -> "()"
    Typ(_) -> "Type"
    Err(msg, _) -> "<error: " <> msg <> ">"
  }
}

fn cases_to_string(cases: List(Case)) -> String {
  list.fold(cases, "", fn(acc, c) {
    acc <> " " <> case_to_string(c)
  })
}

fn case_to_string(case_: Case) -> String {
  "(" <> pattern_to_string(case_.pattern) <> " => " <> term_to_string(case_.body) <> ")"
}

fn pattern_to_string(pat: Pattern) -> String {
  case pat {
    PAny(_) -> "_"
    PVar(name, _) -> name
    PCtr(tag, inner, _) -> tag <> "(" <> pattern_to_string(inner) <> ")"
    PUnit(_) -> "()"
    PLit(Int(value), _) -> int.to_string(value)
    PLit(Float(value), _) -> float.to_string(value)
  }
}

/// Format a value for debugging / display.
pub fn value_to_string(value: Value) -> String {
  case value {
    VNeut(head, spine) ->
      case spine {
        [] -> neut_head_to_string(head)
        _ -> neut_to_string(head, spine)
      }
    VLam(#(name, _param), body) ->
      "λ" <> name <> "." <> term_to_string(body)
    VPi(domain, codomain) ->
      "Π" <> value_to_string(domain) <> "." <> value_to_string(codomain)
    VLit(Int(value)) -> int.to_string(value)
    VLit(Float(value)) -> float.to_string(value)
    VCtr(tag, arg) -> tag <> "(" <> value_to_string(arg) <> ")"
    VUnit -> "()"
    VErr -> "<error>"
  }
}

fn neut_head_to_string(head: Head) -> String {
  case head {
    HVar(level) -> "v" <> int.to_string(level)
    HHole(id) -> "?" <> int.to_string(id)
  }
}

fn neut_to_string(head: Head, spine: List(Elim)) -> String {
  let head_str = neut_head_to_string(head)
  let spine_str = list.fold(
    spine,
    "",
    fn(acc, e) {
      let s = case e {
        EApp(arg) -> "(" <> value_to_string(arg) <> ")"
      }
      acc <> s
    },
  )
  head_str <> spine_str
}
