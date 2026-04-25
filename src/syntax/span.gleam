/// Source location information for tokens and AST nodes.

import gleam/int
///
/// Spans track where in the source code something appears, which is
/// essential for accurate error messages.

/// A source location within a file, defined by line and column (1-indexed).
///
/// `start` and `end` together define the inclusive range of the source
/// text. `end_line` and `end_col` mark the position after the last
/// character for a more natural half-open interval.
pub type Span {
  Span(
    file: String,
    start_line: Int,
    start_col: Int,
    end_line: Int,
    end_col: Int,
  )
}

/// Create a span from a single character position.
pub fn single(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col + 1)
}

/// Create an empty span at the given position.
pub fn empty(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col)
}

/// Extend a span to include a character immediately after it.
pub fn after(span: Span) -> Span {
  case span.end_line == span.start_line {
    True -> Span(
      span.file,
      span.start_line,
      span.start_col,
      span.end_line,
      span.end_col + 1,
    )
    False -> Span(
      span.file,
      span.start_line,
      span.start_col,
      span.end_line + 1,
      1,
    )
  }
}

/// Merge two spans into the smallest span that contains both.
///
/// Both spans must be from the same file.
pub fn merge(a: Span, b: Span) -> Span {
  case a.start_line < b.start_line || {
    a.start_line == b.start_line && a.start_col <= b.start_col
  } {
    True -> Span(
      a.file,
      a.start_line,
      a.start_col,
      b.end_line,
      b.end_col,
    )
    False -> Span(
      b.file,
      b.start_line,
      b.start_col,
      a.end_line,
      a.end_col,
    )
  }
}

/// Check if this span contains another span.
/// Both spans must be from the same file.
pub fn contains(outer: Span, inner: Span) -> Bool {
  case outer, inner {
    outer, inner
      if outer.file == inner.file
      && outer.start_line < inner.start_line ->
      True
    outer, inner
      if outer.file == inner.file
      && outer.start_line == inner.start_line
      && outer.start_col <= inner.start_col ->
      True
    outer, inner
      if outer.file == inner.file
      && outer.end_line > inner.end_line ->
      True
    outer, inner
      if outer.file == inner.file
      && outer.end_line == inner.end_line
      && outer.end_col >= inner.end_col ->
      True
    _, _ -> False
  }
}

/// Get the number of lines covered by this span.
pub fn line_count(span: Span) -> Int {
  span.end_line - span.start_line + 1
}

/// Get the filename for this span.
pub fn file(span: Span) -> String {
  span.file
}

/// Get the number of columns (characters) covered by this span.
/// Only meaningful for single-line spans.
pub fn column_count(span: Span) -> Int {
  case span.end_line == span.start_line {
    True -> span.end_col - span.start_col
    False -> -1 // Multi-line, use line_count instead
  }
}

/// Format a span for display in error messages.
pub fn to_string(span: Span) -> String {
  "in "
  <> span.file
  <> " "
  <> case span.start_line == span.end_line {
    True ->
      "line "
      <> int.to_string(span.start_line)
      <> ", col "
      <> int.to_string(span.start_col)
    False ->
      "lines "
      <> int.to_string(span.start_line)
      <> "-"
      <> int.to_string(span.end_line)
      <> ", col "
      <> int.to_string(span.start_col)
  }
}

// Format a span concisely as "file:L:C".
pub fn to_short_string(span: Span) -> String {
  span.file
  <> ":"
  <> int.to_string(span.start_line)
  <> ":"
  <> int.to_string(span.start_col)
}

/// Compare spans for equality.
/// Spans are equal if the file and all coordinate fields match.
pub fn equals(a: Span, b: Span) -> Bool {
  a.file == b.file
  && a.start_line == b.start_line
  && a.start_col == b.start_col
  && a.end_line == b.end_line
  && a.end_col == b.end_col
}
