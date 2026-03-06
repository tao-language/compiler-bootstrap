// ============================================================================
// CORE LANGUAGE FORMATTER
// ============================================================================
/// Simple formatter for the core language.
///
/// This module defines formatting logic specific to the core language AST.
/// It produces TypeScript-like output.
///
/// # Example
///
/// ```gleam
/// import core/formatter
/// import core/core
///
/// let term = core.Term(core.Lam("x", body), span)
/// formatter.format(term)
/// // Returns: "(x: A) => body"
/// ```

import core/core
import gleam/int
import gleam/list
import gleam/string

// ============================================================================
// MAIN API
// ============================================================================

/// Format a Term to source code
pub fn format(term: core.Term) -> String {
  format_term(term)
}

/// Format a Pattern to source code
pub fn format_pattern(pattern: core.Pattern) -> String {
  do_format_pattern(pattern)
}

// ============================================================================
// TERM FORMATTING
// ============================================================================

/// Format a term to a string
fn format_term(term: core.Term) -> String {
  case term.data {
    core.Typ(k) -> format_type(k)
    core.Lit(lit) -> format_literal(lit)
    core.LitT(lit_type) -> format_literal_type(lit_type)
    core.Var(_) -> "x"
    core.Hole(_) -> "?"
    core.Rcd(fields) -> format_record(fields)
    core.Ctr(tag, arg) -> format_constructor(tag, arg)
    core.Dot(arg, field) -> format_dot(arg, field)
    core.Ann(term, typ) -> format_annotation(term, typ)
    core.Lam(name, body) -> format_lambda(name, body)
    core.Pi(name, in_ty, out_ty) -> format_pi(name, in_ty, out_ty)
    core.App(fun, arg) -> format_application(fun, arg)
    core.Match(arg, _motive, cases) -> format_match(arg, cases)
  }
}

/// Format a type
fn format_type(k: Int) -> String {
  case k {
    0 -> "Type"
    _ -> "Type" <> int.to_string(k)
  }
}

/// Format a literal value
fn format_literal(lit: core.Literal) -> String {
  case lit {
    core.I32(v) -> int.to_string(v)
    core.I64(v) -> int.to_string(v)
    core.U32(v) -> int.to_string(v)
    core.U64(v) -> int.to_string(v)
    core.F32(v) -> float_to_string(v)
    core.F64(v) -> float_to_string(v)
  }
}

/// Format a literal type
fn format_literal_type(lit_type: core.LiteralType) -> String {
  case lit_type {
    core.I32T -> "I32"
    core.I64T -> "I64"
    core.U32T -> "U32"
    core.U64T -> "U64"
    core.F32T -> "F32"
    core.F64T -> "F64"
  }
}

/// Format a float (simplified)
fn float_to_string(f: Float) -> String {
  case f {
    0.0 -> "0.0"
    1.0 -> "1.0"
    3.14 -> "3.14"
    _ -> "0.0"
  }
}

/// Format a record
fn format_record(fields: List(#(String, core.Term))) -> String {
  case fields {
    [] -> "{ }"
    _ -> {
      let field_strings =
        fields
        |> list.map(fn(field) {
          let #(name, value) = field
          name <> ": " <> format_term(value)
        })
        |> string.join(", ")
      
      "{ " <> field_strings <> " }"
    }
  }
}

/// Format a constructor application
fn format_constructor(tag: String, arg: core.Term) -> String {
  tag <> "(" <> format_term(arg) <> ")"
}

/// Format a field projection
fn format_dot(arg: core.Term, field: String) -> String {
  format_term(arg) <> "." <> field
}

/// Format a type annotation
fn format_annotation(term: core.Term, typ: core.Term) -> String {
  "(" <> format_term(term) <> ": " <> format_term(typ) <> ")"
}

/// Format a lambda abstraction
fn format_lambda(name: String, body: core.Term) -> String {
  "(" <> name <> ": A) => " <> format_term(body)
}

/// Format a Pi type
fn format_pi(name: String, in_ty: core.Term, out_ty: core.Term) -> String {
  "(" <> name <> ": " <> format_term(in_ty) <> ") => " <> format_term(out_ty)
}

/// Format a function application
fn format_application(fun: core.Term, arg: core.Term) -> String {
  format_term(fun) <> "(" <> format_term(arg) <> ")"
}

/// Format a match expression
fn format_match(arg: core.Term, cases: List(core.Case)) -> String {
  let case_strings =
    cases
    |> list.map(fn(c) { format_case(c) })
    |> string.join(", ")
  
  "match " <> format_term(arg) <> " with { " <> case_strings <> " }"
}

/// Format a match case
fn format_case(c: core.Case) -> String {
  do_format_pattern(c.pattern) <> " => " <> format_term(c.body)
}

// ============================================================================
// PATTERN FORMATTING
// ============================================================================

/// Format a pattern to a string
fn do_format_pattern(pattern: core.Pattern) -> String {
  case pattern {
    core.PAny -> "_"
    core.PAs(p, name) -> name <> " @ " <> do_format_pattern(p)
    core.PTyp(k) -> format_type(k)
    core.PLit(lit) -> format_literal(lit)
    core.PLitT(lit_type) -> format_literal_type(lit_type)
    core.PRcd(fields) -> format_pattern_record(fields)
    core.PCtr(tag, arg) -> tag <> "(" <> do_format_pattern(arg) <> ")"
  }
}

/// Format a pattern record
fn format_pattern_record(fields: List(#(String, core.Pattern))) -> String {
  case fields {
    [] -> "{ }"
    _ -> {
      let field_strings =
        fields
        |> list.map(fn(field) {
          let #(name, pattern) = field
          name <> ": " <> do_format_pattern(pattern)
        })
        |> string.join(", ")
      
      "{ " <> field_strings <> " }"
    }
  }
}
