// ============================================================================
// ERROR REPORTING
// ============================================================================
/// Convert parse and type errors to diagnostics with source snippets.
import core/core.{ArityMismatch, ComptimePermissionDenied, CtrUndefined, HoleUnsolved, MatchMissingCase, MatchRedundantCase, NotAFunction, type Error as TypeError, TypeMismatch, VarUndefined}
import gleam/int
import gleam/option.{None}
import gleam/string
import syntax/grammar.{ParseError, ParseErrorWithSpan, type Span}
import syntax/source_snippet

// ============================================================================
// PARSE ERROR TO DIAGNOSTIC
// ============================================================================

pub fn parse_error_to_diagnostic(error: grammar.ParseError, source: String, file: String) -> source_snippet.Diagnostic {
  case error {
    ParseError(position: pos, expected: exp, got: g) -> {
      // Convert character position to line/column
      let span = position_to_span(source, pos, file)

      source_snippet.Diagnostic(
        code: "E0001",
        severity: source_snippet.Error,
        message: "Unexpected token",
        primary_span: span,
        spans: [],
        notes: ["Expected: " <> exp, "Got: " <> g],
        hints: ["Check syntax near this position"],
      )
    }
    ParseErrorWithSpan(span: span, expected: exp, got: g, context: ctx) -> {
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
    TypeMismatch(_expected, _got, span1, span2) -> {
      source_snippet.Diagnostic(
        code: "E0101",
        severity: source_snippet.Error,
        message: "Type mismatch",
        primary_span: source_snippet.Span(span1.file, span1.start_line, span1.start_col, span1.end_line, span1.end_col),
        spans: [
          source_snippet.Highlight(
            span: source_snippet.Span(span2.file, span2.start_line, span2.start_col, span2.end_line, span2.end_col),
            style: source_snippet.Secondary,
            label: None,
          ),
        ],
        notes: [],
        hints: ["Check that types are compatible"],
      )
    }
    VarUndefined(_index, span) -> {
      source_snippet.Diagnostic(
        code: "E0102",
        severity: source_snippet.Error,
        message: "Undefined variable",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: [],
        hints: ["Check variable name and scope"],
      )
    }
    HoleUnsolved(id, span) -> {
      source_snippet.Diagnostic(
        code: "E0106",
        severity: source_snippet.Error,
        message: "Unsolved hole",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: ["Hole #" <> int.to_string(id) <> " was not solved during type checking"],
        hints: ["Provide a type annotation or check your term"],
      )
    }
    NotAFunction(_, _) -> {
      source_snippet.Diagnostic(
        code: "E0103",
        severity: source_snippet.Error,
        message: "Not a function",
        primary_span: source_snippet.Span(file, 0, 0, 0, 0),
        spans: [],
        notes: [],
        hints: ["Only functions can be applied"],
      )
    }
    ArityMismatch(span1, span2) -> {
      source_snippet.Diagnostic(
        code: "E0104",
        severity: source_snippet.Error,
        message: "Arity mismatch",
        primary_span: source_snippet.Span(span1.file, span1.start_line, span1.start_col, span1.end_line, span1.end_col),
        spans: [
          source_snippet.Highlight(
            span: source_snippet.Span(span2.file, span2.start_line, span2.start_col, span2.end_line, span2.end_col),
            style: source_snippet.Secondary,
            label: None,
          ),
        ],
        notes: [],
        hints: ["Check the number of arguments"],
      )
    }
    CtrUndefined(tag, span) -> {
      source_snippet.Diagnostic(
        code: "E0105",
        severity: source_snippet.Error,
        message: "Undefined constructor",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: [],
        hints: ["Constructor '" <> tag <> "' is not defined"],
      )
    }
    MatchRedundantCase(span) -> {
      source_snippet.Diagnostic(
        code: "E0202",
        severity: source_snippet.Error,
        message: "Redundant match case",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: [],
        hints: ["Remove the redundant case or reorder patterns"],
      )
    }
    MatchMissingCase(span, _pattern) -> {
      source_snippet.Diagnostic(
        code: "E0201",
        severity: source_snippet.Error,
        message: "Missing match case",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: [],
        hints: ["Add a case for the missing pattern"],
      )
    }
    ComptimePermissionDenied(operation, span, _required) -> {
      source_snippet.Diagnostic(
        code: "E0301",
        severity: source_snippet.Error,
        message: "Permission denied",
        primary_span: source_snippet.Span(span.file, span.start_line, span.start_col, span.end_line, span.end_col),
        spans: [],
        notes: ["Operation '" <> operation <> "' requires permission"],
        hints: ["Add appropriate permission flag"],
      )
    }
    _ -> {
      // Fallback for other error types
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

fn position_to_span(source: String, pos: Int, file: String) -> source_snippet.Span {
  let lines = string.split(source, "\n")
  let #(line, col) = find_line_col(lines, pos)

  source_snippet.Span(file, line, col, line, col + 1)
}

fn find_line_col(lines: List(String), target_pos: Int) -> #(Int, Int) {
  find_line_col_loop(lines, target_pos, 1, 0)
}

fn find_line_col_loop(
  lines: List(String),
  target_pos: Int,
  current_line: Int,
  current_pos: Int,
) -> #(Int, Int) {
  case lines {
    [] -> #(current_line, target_pos - current_pos + 1)
    [line, ..rest] -> {
      let line_len = string.length(line) + 1  // +1 for newline
      case current_pos + line_len > target_pos {
        True -> #(current_line, target_pos - current_pos + 1)
        False -> find_line_col_loop(rest, target_pos, current_line + 1, current_pos + line_len)
      }
    }
  }
}

// ============================================================================
// FORMAT DIAGNOSTIC
// ============================================================================

pub fn format_diagnostic(diagnostic: source_snippet.Diagnostic, source: String) -> String {
  source_snippet.format_diagnostic(diagnostic, source)
}
