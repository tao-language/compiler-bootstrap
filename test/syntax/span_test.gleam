import gleeunit
import syntax/span.{Span, single, empty, after, merge, contains, line_count, column_count, to_string, to_short_string, equals}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Single span creation
// ============================================================================

pub fn single_creates_span_with_correct_positions_test() {
  let s = single("test.gleam", 1, 5)
  assert s.start_line == 1
  assert s.start_col == 5
  assert s.end_line == 1
  assert s.end_col == 6
}

pub fn empty_creates_zero_width_span_test() {
  let s = empty("test.gleam", 1, 5)
  assert s.start_line == 1
  assert s.start_col == 5
  assert s.end_line == 1
  assert s.end_col == 5
}

// ============================================================================
// After (extend span)
// ============================================================================

pub fn after_extends_single_line_span_by_one_column_test() {
  let s = Span("test.gleam", 1, 1, 1, 3)
  let extended = after(s)
  assert extended.start_line == 1
  assert extended.start_col == 1
  assert extended.end_line == 1
  assert extended.end_col == 4
}

pub fn after_extends_span_past_end_of_line_test() {
  let s = Span("test.gleam", 1, 1, 1, 5)
  let extended = after(s)
  assert extended.start_line == 1
  assert extended.start_col == 1
  assert extended.end_line == 1
  assert extended.end_col == 6
}

// ============================================================================
// Merge spans
// ============================================================================

pub fn merge_returns_span_covering_both_when_first_starts_before_second_test() {
  let a = Span("test.gleam", 1, 1, 1, 3)
  let b = Span("test.gleam", 1, 5, 1, 7)
  let merged = merge(a, b)
  assert merged.start_line == 1
  assert merged.start_col == 1
  assert merged.end_line == 1
  assert merged.end_col == 7
}

pub fn merge_returns_span_covering_both_when_second_starts_before_first_test() {
  let a = Span("test.gleam", 1, 5, 1, 7)
  let b = Span("test.gleam", 1, 1, 1, 3)
  let merged = merge(a, b)
  assert merged.start_line == 1
  assert merged.start_col == 1
  assert merged.end_line == 1
  assert merged.end_col == 7
}

// ============================================================================
// Contains
// ============================================================================

pub fn span_contains_itself_test() {
  let s = Span("test.gleam", 1, 1, 1, 5)
  assert contains(s, s)
}

pub fn span_contains_smaller_span_on_same_line_test() {
  let outer = Span("test.gleam", 1, 1, 1, 10)
  let inner = Span("test.gleam", 1, 3, 1, 7)
  assert contains(outer, inner)
}

pub fn span_does_not_contain_span_on_different_line_test() {
  let outer = Span("test.gleam", 1, 1, 1, 5)
  let inner = Span("test.gleam", 2, 1, 2, 5)
  assert contains(outer, inner) == False
}

pub fn span_does_not_contain_span_from_different_file_test() {
  let outer = Span("file1.gleam", 1, 1, 1, 5)
  let inner = Span("file2.gleam", 1, 1, 1, 5)
  assert !contains(outer, inner)
}

// ============================================================================
// Line and column count
// ============================================================================

pub fn line_count_for_single_line_span_is_one_test() {
  let s = Span("test.gleam", 1, 1, 1, 5)
  assert line_count(s) == 1
}

pub fn line_count_for_multi_line_span_test() {
  let s = Span("test.gleam", 1, 1, 3, 5)
  assert line_count(s) == 3
}

pub fn column_count_for_single_line_span_test() {
  let s = Span("test.gleam", 1, 1, 1, 5)
  assert column_count(s) == 4
}

pub fn column_count_for_multi_line_span_is_negative_test() {
  let s = Span("test.gleam", 1, 1, 3, 5)
  assert column_count(s) == -1
}

// ============================================================================
// String representation
// ============================================================================

pub fn to_string_for_single_line_span_test() {
  let s = Span("test.gleam", 1, 5, 1, 10)
  assert to_string(s) == "in test.gleam line 1, col 5"
}

pub fn to_string_for_multi_line_span_test() {
  let s = Span("test.gleam", 1, 5, 3, 10)
  assert to_string(s) == "in test.gleam lines 1-3, col 5"
}

pub fn to_short_string_for_single_line_span_test() {
  let s = Span("test.gleam", 1, 5, 1, 10)
  assert to_short_string(s) == "test.gleam:1:5"
}

pub fn to_short_string_for_multi_line_span_test() {
  let s = Span("test.gleam", 1, 5, 3, 10)
  assert to_short_string(s) == "test.gleam:1:5"
}

// ============================================================================
// Equality
// ============================================================================

pub fn equals_returns_true_for_identical_spans_test() {
  let a = Span("test.gleam", 1, 1, 1, 5)
  let b = Span("test.gleam", 1, 1, 1, 5)
  assert equals(a, b)
}

pub fn equals_returns_false_for_different_start_position_test() {
  let a = Span("test.gleam", 1, 1, 1, 5)
  let b = Span("test.gleam", 1, 2, 1, 5)
  assert !equals(a, b)
}

pub fn equals_returns_false_for_different_file_test() {
  let a = Span("file1.gleam", 1, 1, 1, 5)
  let b = Span("file2.gleam", 1, 1, 1, 5)
  assert !equals(a, b)
}
