// ============================================================================
// ERROR REPORTING
// ============================================================================
/// Convert parse and type errors to diagnostics with source snippets.
import core/ast as ast
import core/state.{
  type Error as TypeError,
  TypeMismatch, VarUndefined, HoleUnsolved, NotAFunction,
  ArityMismatch, CtrUndefined, MatchRedundantCase, MatchMissingCase,
  ComptimePermissionDenied, InfiniteType,
  RcdMissingFields, CtrUnsolvedParam, DotFieldNotFound, DotOnNonCtr,
  SpineMismatch, TODO, PatternMismatch, SyntaxError,
}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{None, Some}
import gleam/string
import syntax/grammar.{ParseError, Span, type Span}
import syntax/source_snippet

// ============================================================================
// PARSE ERROR TO DIAGNOSTIC
// ============================================================================

pub fn parse_error_to_diagnostic(error: grammar.ParseError, _source: String, _file: String) -> source_snippet.Diagnostic {
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
    TypeMismatch(expected, got, expected_span: grammar_span1, got_span: grammar_span2) -> {
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
    ArityMismatch(span1, span2) -> {
      source_snippet.Diagnostic(
        code: "E0104",
        severity: source_snippet.Error,
        message: "Wrong number of arguments",
        primary_span: span_to_source_snippet_span(span1),
        spans: [
          source_snippet.Highlight(
            span: span_to_source_snippet_span(span2),
            style: source_snippet.Secondary,
            label: Some("function defined here"),
          ),
        ],
        notes: [
          "Expected a different number of arguments",
          "Functions in this language are curried - each parameter needs its own arrow"
        ],
        hints: [
          "Check the function signature and provide the correct number of arguments",
          "Remember: f(x, y) applies f to a tuple, while f(x)(y) is curried application",
          "Use a type annotation to clarify the expected arity"
        ],
      )
    }
    CtrUndefined(tag, span) -> {
      source_snippet.Diagnostic(
        code: "E0105",
        severity: source_snippet.Error,
        message: "Constructor not found",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Constructor `" <> tag <> "` is not defined in the current scope",
          "Constructors must be defined before use, typically in a data type declaration"
        ],
        hints: [
          "Check the constructor name for typos",
          "Make sure the constructor is defined in the current scope",
          "Define a type with this constructor first"
        ],
      )
    }
    InfiniteType(hole_id, ty, span1, span2) -> {
      let ty_str = value_to_string(ty)
      source_snippet.Diagnostic(
        code: "E0107",
        severity: source_snippet.Error,
        message: "Infinite type",
        primary_span: span_to_source_snippet_span(span1),
        spans: [
          source_snippet.Highlight(
            span: span_to_source_snippet_span(span2),
            style: source_snippet.Secondary,
            label: Some("occurs in " <> ty_str),
          ),
        ],
        notes: [
          "Hole #" <> int.to_string(hole_id) <> " would create an infinite type",
          "This happens when a type refers to itself",
          "Infinite types like T = T -> ? are not allowed"
        ],
        hints: [
          "Check for recursive type definitions",
          "Add a type annotation to break the cycle",
          "Consider using a fixpoint combinator instead"
        ],
      )
    }
    RcdMissingFields(names, span) -> {
      source_snippet.Diagnostic(
        code: "E0108",
        severity: source_snippet.Error,
        message: "Missing record fields",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Missing fields: " <> string.join(names, ", "),
          "Records must include all defined fields"
        ],
        hints: [
          "Provide all required fields for this record",
          "Check the record definition for the complete field list",
          "Add the missing fields with appropriate values"
        ],
      )
    }
    CtrUnsolvedParam(tag, _ctr, id, span) -> {
      source_snippet.Diagnostic(
        code: "E0109",
        severity: source_snippet.Error,
        message: "Constructor parameter unsolved",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Parameter for constructor `" <> tag <> "` could not be inferred",
          "Hole #" <> int.to_string(id) <> " remains unsolved"
        ],
        hints: [
          "Add a type annotation to help inference",
          "Provide more context for the constructor application",
          "Check that the constructor is fully applied"
        ],
      )
    }
    DotFieldNotFound(name, fields, span) -> {
      let available = list.map(fields, fn(f) { f.0 }) |> string.join(", ")
      source_snippet.Diagnostic(
        code: "E0110",
        severity: source_snippet.Error,
        message: "Field not found",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Field `" <> name <> "` not found",
          "Available fields: " <> available
        ],
        hints: [
          "Check the field name for typos",
          "Use one of the available fields listed above",
          "Add the field to the record definition if needed"
        ],
      )
    }
    DotOnNonCtr(_value, name, span) -> {
      source_snippet.Diagnostic(
        code: "E0111",
        severity: source_snippet.Error,
        message: "Cannot access field on non-record",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Cannot access field `" <> name <> "` on this value",
          "Field access (.field) only works on records"
        ],
        hints: [
          "Use a record value instead of a primitive",
          "Check that you're accessing a record, not a number or other type",
          "Wrap the value in a record: {value: x}.field"
        ],
      )
    }
    SpineMismatch(span1, span2) -> {
      source_snippet.Diagnostic(
        code: "E0112",
        severity: source_snippet.Error,
        message: "Function application mismatch",
        primary_span: span_to_source_snippet_span(span1),
        spans: [
          source_snippet.Highlight(
            span: span_to_source_snippet_span(span2),
            style: source_snippet.Secondary,
            label: Some("application context"),
          ),
        ],
        notes: [
          "Function application has incompatible types",
          "The function's expected arguments don't match the provided arguments"
        ],
        hints: [
          "Check that the function and argument types match",
          "Review the function's type signature",
          "Add type annotations to clarify expectations"
        ],
      )
    }
    PatternMismatch(_pattern, expected_type, pattern_span, value_span) -> {
      let expected_str = value_to_string(expected_type)
      source_snippet.Diagnostic(
        code: "E0201",
        severity: source_snippet.Error,
        message: "Pattern type mismatch",
        primary_span: span_to_source_snippet_span(pattern_span),
        spans: [
          source_snippet.Highlight(
            span: span_to_source_snippet_span(value_span),
            style: source_snippet.Secondary,
            label: Some("expected " <> expected_str),
          ),
        ],
        notes: [
          "Pattern has incompatible type",
          "The pattern expects " <> expected_str <> " but the matched value has a different type"
        ],
        hints: [
          "Use a pattern that matches " <> expected_str,
          "Check the type of the value being matched",
          "Consider adding a type annotation to clarify expectations"
        ],
      )
    }
    MatchMissingCase(span, _pattern) -> {
      source_snippet.Diagnostic(
        code: "E0202",
        severity: source_snippet.Error,
        message: "Pattern match not exhaustive",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Pattern match is not exhaustive",
          "Missing case for pattern"
        ],
        hints: [
          "Add a case for the missing pattern",
          "Consider using a wildcard pattern `_` to handle all remaining cases",
          "Ensure all constructors are covered for complete safety"
        ],
      )
    }
    MatchRedundantCase(span) -> {
      source_snippet.Diagnostic(
        code: "E0203",
        severity: source_snippet.Error,
        message: "Redundant pattern",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "This case is already handled by a previous pattern",
          "Redundant cases indicate dead code that will never execute"
        ],
        hints: [
          "Remove the redundant case",
          "Or use a different guard condition",
          "Reorder cases to put specific patterns before wildcards"
        ],
      )
    }
    ComptimePermissionDenied(operation, span, required) -> {
      source_snippet.Diagnostic(
        code: "E0501",
        severity: source_snippet.Error,
        message: "Permission denied",
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Operation '" <> operation <> "' requires permission",
          "Required permissions: " <> int.to_string(list.length(required))
        ],
        hints: [
          "Add the appropriate permission flag to your comptime block",
          "Move the operation to runtime (outside comptime)",
          "Review comptime permission requirements in the documentation"
        ],
      )
    }
    TODO(message) -> {
      source_snippet.Diagnostic(
        code: "E9999",
        severity: source_snippet.Error,
        message: "TODO: Not yet implemented",
        primary_span: source_snippet.Span(file, 0, 0, 0, 1),
        spans: [],
        notes: [
          message,
          "This is a placeholder for incomplete code"
        ],
        hints: [
          "This feature is not yet implemented",
          "Implement the missing functionality",
          "Replace TODO with actual implementation"
        ],
      )
    }
    SyntaxError(span, expected, got, context) -> {
      source_snippet.Diagnostic(
        code: "E0001",
        severity: source_snippet.Error,
        message: "Syntax error" <> case context {
          "" -> ""
          _ -> " in " <> context
        },
        primary_span: span_to_source_snippet_span(span),
        spans: [],
        notes: [
          "Expected: " <> expected,
          "Got: " <> got
        ],
        hints: [
          "Check for typos or missing tokens",
          "Ensure expressions are well-formed",
          "Review the syntax documentation"
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
    ast.VTyp(universe) -> "%Type(" <> int.to_string(universe) <> ")"
    ast.VLit(literal) -> literal_to_string(literal)
    ast.VLitT(literal_type) -> literal_type_to_string(literal_type)
    ast.VNeut(head, spine) -> neutral_to_string(head, spine)
    ast.VRcd(fields) -> record_fields_to_string(fields)
    ast.VCtrValue(ctr) -> ctr_value_to_string(ctr)
    ast.VLam(implicit, name, _env, _body) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      "%fn" <> implicit_str <> "(" <> name <> ") { ... }"
    }
    ast.VPi(implicit, name, _env, in_val, _out) -> {
      let implicit_str = case implicit {
        [] -> ""
        _ -> "<" <> string.join(implicit, ", ") <> ">"
      }
      "%pi" <> implicit_str <> "(" <> name <> ": " <> value_to_string(in_val) <> ") -> ..."
    }
    ast.VRecord(fields) -> {
      "{" <> string.join(list.map(fields, fn(f) { f.0 <> ": ..." }), ", ") <> "}"
    }
    ast.VCall(name, args) -> {
      name <> "(" <> args |> list.map(value_to_string) |> string.join(", ") <> ")"
    }
    ast.VFix(_name, _env, _body) -> "fix(...)"
    ast.VUnit -> "Unit"
    ast.VErr -> "<error>"
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
    ast.I32(n) -> int.to_string(n)
    ast.I64(n) -> int.to_string(n) <> "i64"
    ast.U32(n) -> int.to_string(n) <> "u32"
    ast.U64(n) -> int.to_string(n) <> "u64"
    ast.F32(f) -> float.to_string(f) <> "f32"
    ast.F64(f) -> float.to_string(f)
  }
}

fn literal_type_to_string(literal_type) -> String {
  case literal_type {
    ast.I32T -> "Int"
    ast.I64T -> "Int64"
    ast.U32T -> "UInt32"
    ast.U64T -> "UInt64"
    ast.F32T -> "Float32"
    ast.F64T -> "Float"
  }
}

fn head_to_string(head) -> String {
  case head {
    ast.HVar(level) -> "var[" <> int.to_string(level) <> "]"
    ast.HHole(id) -> "?" <> int.to_string(id)
    ast.HStepLimit -> "<step-limit>"
  }
}

fn ctr_value_to_string(ctr: ast.CtrValue) -> String {
  case ctr {
    ast.VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
  }
}

fn record_fields_to_string(fields: List(#(String, ast.Value))) -> String {
  fields
  |> list.map(fn(f: #(String, ast.Value)) { f.0 <> ": " <> value_to_string(f.1) })
  |> string.join(", ")
  |> fn(s) { "{" <> s <> "}" }
}

// Helper function to get span from a term
fn get_term_span(_term) -> grammar.Span {
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
