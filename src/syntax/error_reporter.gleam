// ============================================================================
// ERROR REPORTING
// ============================================================================
/// Convert parse errors to diagnostics with source snippets.
import gleam/int
import gleam/list
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
