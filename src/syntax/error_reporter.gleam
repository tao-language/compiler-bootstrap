// ============================================================================
// ERROR REPORTING
// ============================================================================
/// Convert parse and type errors to diagnostics with source snippets.
import core/core.{
  type Error as TypeError,
  TypeMismatch, VarUndefined, HoleUnsolved, NotAFunction,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{None}
import gleam/string
import syntax/grammar.{ParseError, Span, type Span}
import syntax/source_snippet

// ============================================================================
// PARSE ERROR TO DIAGNOSTIC
// ============================================================================

pub fn parse_error_to_diagnostic(error: grammar.ParseError, source: String, file: String) -> source_snippet.Diagnostic {
  case error {
    ParseError(span: span, expected: exp, got: g, context: ctx) -> {
      source_snippet.Diagnostic(
        code: "E0001",
        severity: source_snippet.Error,
        message: "Syntax error" <> case ctx {
          "" -> ""
          _ -> " in " <> ctx
        },
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: ["Expected: " <> exp, "Got: " <> g],
        hints: [],
      )
    }
  }
}

// ============================================================================
// TYPE ERROR TO DIAGNOSTIC
// ============================================================================

pub fn type_error_to_diagnostic(error: TypeError, source: String, file: String) -> source_snippet.Diagnostic {
  case error {
    TypeMismatch(expected, got, span1: grammar_span1, span2: grammar_span2) -> {
      let expected_str = type_to_string(expected)
      let got_str = type_to_string(got)
      source_snippet.Diagnostic(
        code: "E0101",
        severity: source_snippet.Error,
        message: "Type mismatch",
        primary_span: span_to_source_snippet_span(grammar_span1),
        spans: [
          source_snippet.Highlight(
            span: span_to_source_snippet_span(grammar_span2),
            style: source_snippet.Secondary,
            label: None,
          ),
        ],
        notes: [
          got_str <> " and " <> expected_str <> " are incompatible types",
          "The expression produces " <> got_str <> " but " <> expected_str <> " is expected here"
        ],
        hints: [
          "Check that the expression has the expected type",
          "Consider adding a type annotation",
          "Did you mean to use a different expression?"
        ],
      )
    }
    VarUndefined(index, span) -> {
      source_snippet.Diagnostic(
        code: "E0102",
        severity: source_snippet.Error,
        message: "Undefined variable",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Variable at index " <> int.to_string(index) <> " is not defined in this scope",
          "Variables must be defined before they are used, typically in a let binding or lambda parameter"
        ],
        hints: [
          "Check variable name and scope",
          "Did you forget to define this variable?",
          "Check for typos in the variable name"
        ],
      )
    }
    HoleUnsolved(id, span) -> {
      source_snippet.Diagnostic(
        code: "E0106",
        severity: source_snippet.Error,
        message: "Unsolved hole",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Hole #" <> int.to_string(id) <> " was not solved during type checking",
          "Holes are development placeholders that must be replaced before the program is complete"
        ],
        hints: [
          "Holes are placeholders that must be filled",
          "Provide a term of the expected type, or add a type annotation",
          "Use holes temporarily during development, then replace them"
        ],
      )
    }
    NotAFunction(fun, fun_ty) -> {
      let span = get_term_span(fun)
      let fun_ty_str = value_to_string(fun_ty)
      source_snippet.Diagnostic(
        code: "E0103",
        severity: source_snippet.Error,
        message: "Cannot call non-function value",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "This value has type " <> fun_ty_str <> ", which is not callable",
          "Only function values (created with ->) can be called with parentheses"
        ],
        hints: [
          "Only functions can be called with parentheses",
          "Check that you're calling a function, not a value",
          "If you want a function, use a lambda: x -> expression"
        ],
      )
    }
    _ -> {
      // Fallback for other error types (ArityMismatch, CtrUndefined, PatternMismatch, etc.)
      source_snippet.Diagnostic(
        code: "E9999",
        severity: source_snippet.Error,
        message: "Type error",
        primary_span: source_snippet.Span(file, 0, 0, 0, 0),
        spans: [],
        notes: [],
        hints: [],
      )
    }
  }
}

// Helper function to convert grammar.Span to source_snippet.Span
fn span_to_source_snippet_span(span: grammar.Span) -> source_snippet.Span {
  source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col)
}

// Helper function to convert types to readable strings
fn type_to_string(value) -> String {
  value_to_string(value)
}

// Helper function to convert values to readable strings
fn value_to_string(value) -> String {
  case value {
    core.VTyp(universe) -> "$Type(" <> int.to_string(universe) <> ")"
    core.VLit(literal) -> literal_to_string(literal)
    core.VLitT(literal_type) -> literal_type_to_string(literal_type)
    core.VNeut(head, spine) -> neutral_to_string(head, spine)
    core.VRcd(fields) -> record_fields_to_string(fields)
    core.VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    core.VLam(name, _env, _body) -> "fn(" <> name <> ") { ... }"
    core.VPi(name, _env, in_val, _out) -> {
      "(" <> name <> ": " <> value_to_string(in_val) <> ") -> ..."
    }
    core.VCall(name, args) -> {
      name <> "(" <> args |> list.map(value_to_string) |> string.join(", ") <> ")"
    }
    core.VFix(_name, _env, _body) -> "fix(...)"
    core.VErr -> "<error>"
  }
}

fn neutral_to_string(head, spine) -> String {
  let head_str = head_to_string(head)
  case spine {
    [] -> head_str
    [..] -> head_str <> " ⟨" <> int.to_string(list.length(spine)) <> " operations pending⟩"
  }
}

fn literal_to_string(literal) -> String {
  case literal {
    core.I32(n) -> int.to_string(n)
    core.I64(n) -> int.to_string(n) <> "i64"
    core.U32(n) -> int.to_string(n) <> "u32"
    core.U64(n) -> int.to_string(n) <> "u64"
    core.F32(f) -> float.to_string(f) <> "f32"
    core.F64(f) -> float.to_string(f)
  }
}

fn literal_type_to_string(literal_type) -> String {
  case literal_type {
    core.I32T -> "Int"
    core.I64T -> "Int64"
    core.U32T -> "UInt32"
    core.U64T -> "UInt64"
    core.F32T -> "Float32"
    core.F64T -> "Float"
  }
}

fn head_to_string(head) -> String {
  case head {
    core.HVar(level) -> "var[" <> int.to_string(level) <> "]"
    core.HHole(id) -> "?" <> int.to_string(id)
  }
}

fn record_fields_to_string(fields: List(#(String, core.Value))) -> String {
  fields
  |> list.map(fn(f: #(String, core.Value)) { f.0 <> ": " <> value_to_string(f.1) })
  |> string.join(", ")
  |> fn(s) { "{" <> s <> "}" }
}

// Helper function to get span from a term
fn get_term_span(term) -> grammar.Span {
  // Extract span from term - simplified implementation
  // In a full implementation, this would traverse the term to find the span
  grammar.Span("", 0, 0, 0, 0)
}

// ============================================================================
// FORMAT DIAGNOSTIC
// ============================================================================

pub fn format_diagnostic(diagnostic: source_snippet.Diagnostic, source: String) -> String {
  source_snippet.format_diagnostic(diagnostic, source)
}
