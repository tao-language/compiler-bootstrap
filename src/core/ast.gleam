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
import gleam/option.{type Option, Some, None}
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
  Ann(term: Term, type_: Term, span: Span)
  Call(name: String, args: List(Term), span: Span)
  Rcd(fields: List(#(String, Term)), span: Span)
  Typ(level: Int, span: Span)
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
  Case(pattern: Pattern, guard: Option(Term), body: Term, span: Span)
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
  VLam(param: #(String, Value), body: Term)
  VPi(domain: Value, codomain: Value)
  VLit(value: Literal)
  VCtr(tag: String, arg: Value)
  VRcd(fields: List(#(String, Value)))
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

/// Syntax sugar for let bindings: `let name = value; body`.
///
/// This is desugared to `App(Lam((name, param_type), body), value)` —
/// a beta-reduction application. The `param_type` is typically unit.
pub fn let_var(name: String, param_type: Term, value: Term, body: Term, span: Span) -> Term {
  App(Lam(#(name, param_type), body, span), value, span)
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
    Lam(#(name, param), func_body, span) ->
      Lam(#(name, shift_term_from(param, shift, from)),
          shift_term_from(func_body, shift, from + 1),
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
            list.map(cases, fn(c) {
              Case(c.pattern, shift_opt(c.guard, shift, from), shift_term_from(c.body, shift, from), c.span)
            }),
            span)
    Ann(term, type_, span) ->
      Ann(shift_term_from(term, shift, from),
          shift_term_from(type_, shift, from),
          span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { shift_term_from(a, shift, from) }), span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(f) { #(f.0, shift_term_from(f.1, shift, from)) }), span)
    Typ(level, span) -> Typ(level, span)
    Err(msg, span) -> Err(msg, span)
  }
}

fn shift_opt(term: Option(Term), shift: Int, from: Int) -> Option(Term) {
  case term {
    Some(t) -> Some(shift_term_from(t, shift, from))
    None -> None
  }
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
    Lam(#(name, param_type), func_body, _) ->
      "%fn(" <> name <> ": " <> term_to_string(param_type) <> ") => " <> term_to_string(func_body)
    App(fun, arg, _) ->
      "fun(" <> term_to_string(fun) <> ": " <> term_to_string(arg) <> ")"
    Pi(domain, codomain, _) ->
      "%fn(" <> name_from_pi(domain) <> ": " <> term_to_string(domain) <> ") -> " <> term_to_string(codomain)
    Lit(Int(value), _) -> int.to_string(value)
    Lit(Float(value), _) -> float.to_string(value)
    Ctr(tag, arg, _) ->
      case arg {
        Ann(t, Typ(0, _), _) -> "#" <> tag <> "(" <> term_to_string(t) <> ")"
        Ann(t, _, _) -> "#" <> tag <> "(" <> term_to_string(t) <> ": " <> term_to_string(arg) <> ")"
        _ -> "#" <> tag
      }
    Match(arg, cases, _) ->
      "%match " <> term_to_string(arg) <> " {"
      <> list.fold(cases, "", fn(acc, c) { acc <> "\n  | " <> case_to_string(c) })
      <> "\n}"
    Ann(term, type_, _) ->
      term_to_string(term) <> " : " <> term_to_string(type_)
    Call(name, args, _) ->
      "call(" <> name <> "[" <> list.fold(args, "", fn(acc, a) { case acc { "" -> term_to_string(a) _ -> acc <> ", " <> term_to_string(a) } }) <> "])"
    Rcd(fields, _) ->
      case fields {
        [] -> "()"
        _ -> "{" <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> term_to_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> term_to_string(f.1)
          }
        }) <> "}"
      }
    Typ(level, _) -> "%Type(" <> int.to_string(level) <> ")"
    Err(msg, _) -> "\"" <> msg <> "\""
  }
}

fn name_from_pi(term: Term) -> String {
  case term {
    Ann(t, _, _) ->
      case t {
        Var(i, _) -> "_" <> int.to_string(i)
        Hole(id, _) -> "_" <> int.to_string(id)
        _ -> "_"
      }
    _ -> "_"
  }
}

fn case_to_string(case_: Case) -> String {
  case case_.guard {
    Some(guard) ->
      pattern_to_string(case_.pattern) <> " ? " <> term_to_string(guard)
      <> " => " <> term_to_string(case_.body)
    None ->
      pattern_to_string(case_.pattern) <> " => " <> term_to_string(case_.body)
  }
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
    VLam(#(name, _param_type), body) ->
      "%fn(" <> name <> ") => " <> term_to_string(body)
    VPi(domain, codomain) ->
      "%fn(" <> name_from_pi_value(domain) <> ": " <> value_to_string(domain) <> ") -> " <> value_to_string(codomain)
    VLit(Int(value)) -> int.to_string(value)
    VLit(Float(value)) -> float.to_string(value)
    VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ -> "{" <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> value_to_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> value_to_string(f.1)
          }
        }) <> "}"
      }
    VErr -> "\"error\""
  }
}

fn name_from_pi_value(value: Value) -> String {
  case value {
    VNeut(HVar(level), _) -> "_" <> int.to_string(level)
    VNeut(HHole(id), _) -> "_" <> int.to_string(id)
    _ -> "_"
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
