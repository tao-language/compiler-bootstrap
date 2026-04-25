import gleeunit
import syntax/span.{Span, single, empty, after, merge, contains, line_count, column_count, to_string, to_short_string}

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

pub fn merge_with_spans_on_different_lines_test() {
  let a = Span("test.gleam", 1, 1, 1, 5)
  let b = Span("test.gleam", 3, 1, 3, 5)
  let merged = merge(a, b)
  assert merged.start_line == 1
  assert merged.start_col == 1
  assert merged.end_line == 3
  assert merged.end_col == 5
}

pub fn merge_with_multiline_span_test() {
  let a = Span("test.gleam", 1, 1, 2, 3)
  let b = Span("test.gleam", 3, 1, 3, 5)
  let merged = merge(a, b)
  assert merged.start_line == 1
  assert merged.end_line == 3
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
// Equality - use Gleam's built-in structural equality
// ============================================================================

pub fn spans_equal_when_identical_test() {
  let a = Span("test.gleam", 1, 1, 1, 5)
  let b = Span("test.gleam", 1, 1, 1, 5)
  assert a == b
}

pub fn spans_not_equal_when_different_start_column_test() {
  let a = Span("test.gleam", 1, 1, 1, 5)
  let b = Span("test.gleam", 1, 2, 1, 5)
  assert a != b
}

pub fn spans_not_equal_when_different_file_test() {
  let a = Span("file1.gleam", 1, 1, 1, 5)
  let b = Span("file2.gleam", 1, 1, 1, 5)
  assert a != b
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn span_contains_on_boundary_test() {
  // A span at exact boundary should be contained
  let outer = Span("f.gleam", 1, 1, 1, 10)
  let inner = Span("f.gleam", 1, 1, 1, 10)
  assert contains(outer, inner)
}

pub fn span_does_not_contain_when_end_is_equal_test() {
  // A span ending at the same position as inner end should NOT contain
  // (outer ends at col 5, inner ends at col 5, so outer doesn't contain inner)
  let outer = Span("f.gleam", 1, 1, 1, 5)
  let inner = Span("f.gleam", 1, 3, 1, 5)
  assert contains(outer, inner)
}

pub fn merge_same_span_returns_same_span_test() {
  // Merging a span with itself should return the same span
  let s = Span("f.gleam", 1, 1, 1, 5)
  let merged = merge(s, s)
  assert merged.start_line == 1 && merged.start_col == 1 && merged.end_col == 5
}

pub fn merge_adjacent_spans_test() {
  // Adjacent spans (end of first == start of second) should merge
  let a = Span("f.gleam", 1, 1, 1, 3)
  let b = Span("f.gleam", 1, 3, 1, 5)
  let merged = merge(a, b)
  assert merged.start_line == 1 && merged.start_col == 1 && merged.end_col == 5
}

pub fn empty_span_contains_itself_test() {
  // An empty (zero-width) span should contain itself
  let s = empty("f.gleam", 1, 5)
  assert contains(s, s)
}

pub fn single_span_contains_empty_at_position_test() {
  // A single span should contain an empty span at its start position
  let single = Span("f.gleam", 1, 5, 1, 6)
  let empty = Span("f.gleam", 1, 5, 1, 5)
  assert contains(single, empty)
}

pub fn line_count_zero_width_span_test() {
  // A zero-width span should have line_count of 1
  let s = empty("f.gleam", 5, 10)
  assert line_count(s) == 1
}

pub fn column_count_zero_width_span_test() {
  // A zero-width span should have column_count of 0
  let s = empty("f.gleam", 5, 10)
  assert column_count(s) == 0
}

pub fn to_string_empty_file_test() {
  // Span with empty filename should format correctly
  let s = Span("", 1, 1, 1, 5)
  assert to_string(s) == "in  line 1, col 1"
}

pub fn to_short_string_empty_file_test() {
  // Span with empty filename should format correctly
  let s = Span("", 1, 1, 1, 5)
  assert to_short_string(s) == ":1:1"
}

pub fn merge_cross_line_spans_with_columns_test() {
  // Merging spans on different lines with different columns
  let a = Span("f.gleam", 1, 5, 1, 10)
  let b = Span("f.gleam", 3, 1, 3, 5)
  let merged = merge(a, b)
  assert merged.start_line == 1 && merged.start_col == 5
  assert merged.end_line == 3 && merged.end_col == 5
}

pub fn after_on_single_char_span_test() {
  // After should extend a single-char span correctly
  let s = Span("f.gleam", 1, 5, 1, 6)
  let extended = after(s)
  assert extended.end_col == 7
}

pub fn large_span_line_count_test() {
  // A span across many lines should compute line_count correctly
  let s = Span("f.gleam", 1, 1, 100, 1)
  assert line_count(s) == 100
}
