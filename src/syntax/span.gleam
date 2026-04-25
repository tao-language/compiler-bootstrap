/// Source location information for tokens and AST nodes.
///
/// Spans track where in the source code something appears, which is
/// essential for accurate error messages.
///
/// `start` and `end` together define a half-open interval:
/// `[start_line, start_col)` to `(end_line, end_col]`.

import gleam/int

/// A source location within a file, defined by line and column (1-indexed).
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
///
/// # Example
///
/// ```gleam
/// import syntax/span.{single}
/// let span = single("main.tao", 1, 1)  // Line 1, column 1
/// ```
pub fn single(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col + 1)
}

/// Create an empty span at the given position.
///
/// # Example
///
/// ```gleam
/// import syntax/span.{empty}
/// let span = empty("main.tao", 1, 1)  // Zero-width at line 1, column 1
/// ```
pub fn empty(file: String, line: Int, col: Int) -> Span {
  Span(file, line, col, line, col)
}

/// Extend a span by one column position.
///
/// This is used by the lexer to include a character in the span
/// after it has been consumed.
///
/// # Example
///
/// ```gleam
/// import syntax/span.{single, after}
/// let span = single("main.tao", 1, 1)
/// let extended = after(span)  // Extends to column 2
/// ```
pub fn after(span: Span) -> Span {
  Span(
    span.file,
    span.start_line,
    span.start_col,
    span.end_line,
    span.end_col + 1,
  )
}

/// Merge two spans into the smallest span that contains both.
///
/// Both spans must be from the same file.
///
/// # Example
///
/// ```gleam
/// import syntax/span.{single, merge}
/// let a = single("main.tao", 1, 1)
/// let b = single("main.tao", 1, 5)
/// let merged = merge(a, b)  // Covers columns 1-6
/// ```
pub fn merge(a: Span, b: Span) -> Span {
  case a.start_line < b.start_line || {
    a.start_line == b.start_line && a.start_col <= b.start_col
  } {
    True -> Span(a.file, a.start_line, a.start_col, b.end_line, b.end_col)
    False -> Span(b.file, b.start_line, b.start_col, a.end_line, a.end_col)
  }
}

/// Check if this span contains another span.
/// Both spans must be from the same file.
///
/// # Example
///
/// ```gleam
/// import syntax/span::{Span, contains, single}
/// let outer = Span("main.tao", 1, 1, 1, 10)
/// let inner = Span("main.tao", 1, 3, 1, 7)
/// assert contains(outer, inner)  // True
/// ```
pub fn contains(outer: Span, inner: Span) -> Bool {
  outer.file == inner.file
  && starts_at_or_before(outer, inner)
  && ends_at_or_after(outer, inner)
}

/// Check if outer starts at or before inner.
fn starts_at_or_before(outer: Span, inner: Span) -> Bool {
  outer.start_line < inner.start_line
  || { outer.start_line == inner.start_line && outer.start_col <= inner.start_col }
}

/// Check if outer ends at or after inner.
fn ends_at_or_after(outer: Span, inner: Span) -> Bool {
  outer.end_line > inner.end_line
  || { outer.end_line == inner.end_line && outer.end_col >= inner.end_col }
}

/// Get the number of lines covered by this span.
///
/// # Example
///
/// ```gleam
/// import syntax/span::{line_count, Span}
/// let span = Span("main.tao", 1, 1, 3, 5)
/// assert line_count(span) == 3  // Lines 1, 2, 3
/// ```
pub fn line_count(span: Span) -> Int {
  span.end_line - span.start_line + 1
}

/// Get the number of columns (characters) covered by this span.
/// Only meaningful for single-line spans.
///
/// # Example
///
/// ```gleam
/// import syntax/span::{column_count, Span}
/// let span = Span("main.tao", 1, 1, 1, 5)
/// assert column_count(span) == 4  // 4 characters
/// ```
pub fn column_count(span: Span) -> Int {
  case span.end_line == span.start_line {
    True -> span.end_col - span.start_col
    False -> -1
  }
}

/// Format a span for display in error messages.
///
/// # Example
///
/// ```gleam
/// import syntax/span::{to_string, Span}
/// let span = Span("main.tao", 1, 5, 1, 10)
/// assert to_string(span) == "in main.tao line 1, col 5"
/// ```
pub fn to_string(span: Span) -> String {
  case span.start_line == span.end_line {
    True ->
      "in "
      <> span.file
      <> " line "
      <> int.to_string(span.start_line)
      <> ", col "
      <> int.to_string(span.start_col)
    False ->
      "in "
      <> span.file
      <> " lines "
      <> int.to_string(span.start_line)
      <> "-"
      <> int.to_string(span.end_line)
      <> ", col "
      <> int.to_string(span.start_col)
  }
}

/// Format a span concisely as "file:L:C".
///
/// # Example
///
/// ```gleam
/// import syntax/span::{to_short_string, Span}
/// let span = Span("main.tao", 1, 5, 1, 10)
/// assert to_short_string(span) == "main.tao:1:5"
/// ```
pub fn to_short_string(span: Span) -> String {
  span.file
  <> ":"
  <> int.to_string(span.start_line)
  <> ":"
  <> int.to_string(span.start_col)
}
