/// Source location spans
/// All positions are 1-based to match user expectations.
import gleam/int

pub type Span {
  Span(file: String, line: Int, column: Int)
}

/// Create a dummy span for synthesized nodes
pub fn dummy() -> Span {
  Span(file: "unknown", line: 0, column: 0)
}

/// Create a span from character offsets
pub fn from_offsets(file: String, start: Int, _end: Int) -> Span {
  Span(file: file, line: 1, column: start + 1)
}

/// Pretty print a span
pub fn to_string(span: Span) -> String {
  case span.line {
    0 -> "unknown"
    _ -> "span(" <> span.file <> ":" <> int.to_string(span.line) <> ":" <> int.to_string(span.column) <> ")"
  }
}
