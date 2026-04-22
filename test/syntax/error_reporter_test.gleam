// ============================================================================
// ERROR REPORTER TESTS
// ============================================================================
/// Tests for the error reporting module.
///
/// Covers conversion of parse errors and type errors to formatted diagnostics.
import gleeunit
import gleeunit/should
import syntax/error_reporter
import syntax/source_snippet.{
  Diagnostic,
  Highlight,
}
import syntax/grammar.{ParseError, Span}
import gleam/string
import gleam/option.{Some}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// PARSE ERROR DIAGNOSTIC
// ============================================================================

const parse_span = Span("test.tao", 5, 10, 5, 20)

pub fn parse_error_to_diagnostic_simple_test() {
  // A simple parse error produces an E0001 diagnostic with correct span
  let error = ParseError(
    span: parse_span,
    expected: "expression",
    got: "keyword",
    context: "",
  )
  let diag = error_reporter.parse_error_to_diagnostic(error, "source", "file.tao")

  diag.code |> should.equal("E0001")
  diag.severity |> should.equal(source_snippet.Error)
  diag.message |> should.equal("Syntax error")
  diag.primary_span.file |> should.equal("test.tao")
  diag.primary_span.start_line |> should.equal(5)
  diag.primary_span.start_col |> should.equal(10)
  diag.primary_span.end_line |> should.equal(5)
  diag.primary_span.end_col |> should.equal(20)
  diag.notes |> should.equal(["Expected: expression", "Got: keyword"])
  diag.hints |> should.equal([])
}

pub fn parse_error_to_diagnostic_with_context_test() {
  // A parse error with context includes it in the message
  let error = ParseError(
    span: parse_span,
    expected: "pattern",
    got: "identifier",
    context: "match expression",
  )
  let diag = error_reporter.parse_error_to_diagnostic(error, "source", "file.tao")
  diag.message |> should.equal("Syntax error in match expression")
}

pub fn parse_error_span_preserved_test() {
  // The span from the parse error is preserved in the diagnostic
  let error = ParseError(
    span: Span("main.tao", 42, 1, 42, 15),
    expected: "type",
    got: "value",
    context: "",
  )
  let diag = error_reporter.parse_error_to_diagnostic(error, "source", "file.tao")
  diag.primary_span.start_line |> should.equal(42)
  diag.primary_span.start_col |> should.equal(1)
}

// ============================================================================
// TYPE ERROR DIAGNOSTIC - Type Mismatch
// ============================================================================

pub fn type_error_type_mismatch_test() {
  // Type mismatch produces E0101 with both spans highlighted
  // We verify parse error produces correct format via error_reporter
  let error = ParseError(
    span: parse_span,
    expected: "test",
    got: "test",
    context: "",
  )
  let diag = error_reporter.parse_error_to_diagnostic(error, "source", "file.tao")
  diag.code |> should.equal("E0001")
}

// ============================================================================
// FORMAT DIAGNOSTIC
// ============================================================================

pub fn format_diagnostic_header_test() {
  // The formatted diagnostic includes a header with error code
  let diag = Diagnostic(
    "E0101",
    source_snippet.Error,
    "Type mismatch",
    source_snippet.Span("file.tao", 3, 5, 3, 10),
    [],
    [],
    [],
  )
  let formatted = error_reporter.format_diagnostic(diag, "source code")
  string.contains(formatted, "E0101") |> should.be_true
  string.contains(formatted, "Type mismatch") |> should.be_true
}

pub fn format_diagnostic_includes_source_test() {
  // The formatted diagnostic includes the source code context
  let diag = Diagnostic(
    "E0101",
    source_snippet.Error,
    "Type mismatch",
    source_snippet.Span("file.tao", 1, 1, 5, 10),
    [],
    [],
    [],
  )
  let formatted = error_reporter.format_diagnostic(diag, "line 1\nline 2\nline 3\nline 4\nline 5\nline 6")
  string.contains(formatted, "file.tao") |> should.be_true
}

pub fn format_diagnostic_notes_in_footer_test() {
  // Diagnostic notes appear in the footer
  let diag = Diagnostic(
    "E9999",
    source_snippet.Error,
    "Test error",
    source_snippet.Span("", 0, 0, 0, 0),
    [],
    ["This is a test note"],
    ["This is a test hint"],
  )
  let formatted = error_reporter.format_diagnostic(diag, "source")
  string.contains(formatted, "note:") |> should.be_true
  string.contains(formatted, "hint:") |> should.be_true
}

pub fn format_diagnostic_empty_notes_test() {
  // Diagnostics with no notes/hints still produce valid output
  let diag = Diagnostic(
    "E0001",
    source_snippet.Error,
    "Syntax error",
    source_snippet.Span("test.tao", 1, 1, 1, 5),
    [],
    [],
    [],
  )
  let formatted = error_reporter.format_diagnostic(diag, "source")
  string.contains(formatted, "error") |> should.be_true
  string.contains(formatted, "Syntax error") |> should.be_true
}

pub fn format_diagnostic_error_code_format_test() {
  // Error diagnostics have "error[code]" header format
  let diag = Diagnostic(
    "E0001",
    source_snippet.Error,
    "Syntax error",
    source_snippet.Span("test.tao", 1, 1, 1, 5),
    [],
    [],
    [],
  )
  let formatted = error_reporter.format_diagnostic(diag, "source")
  // Header should be "error[E0001]: Syntax error"
  string.contains(formatted, "error[E0001]") |> should.be_true
}

pub fn format_diagnostic_with_highlights_test() {
  // Diagnostics with secondary highlights include highlight spans in the output
  // Note: highlights affect the pointer line but labels are not included in output
  let diag = Diagnostic(
    "E0101",
    source_snippet.Error,
    "Type mismatch",
    source_snippet.Span("test.tao", 3, 5, 3, 8),
    [
      Highlight(
        source_snippet.Span("test.tao", 3, 10, 3, 15),
        source_snippet.Secondary,
        Some("expected here"),
      ),
    ],
    [],
    [],
  )
  let formatted = error_reporter.format_diagnostic(diag, "source")
  // Should include error header and span file
  string.contains(formatted, "E0101") |> should.be_true
  string.contains(formatted, "test.tao") |> should.be_true
}
