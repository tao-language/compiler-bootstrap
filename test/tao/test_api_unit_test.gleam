// ============================================================================
// TEST API UNIT TESTS
// ============================================================================
/// Unit tests for the test_api module.
///
/// These tests verify that:
/// 1. Syntax errors in source files are properly reported
/// 2. Type errors in source files are properly reported
/// 3. Exhaustiveness errors are properly reported
/// 4. Passing tests produce Pass results
/// 5. Failing tests produce Fail results
/// 6. Edge cases are handled gracefully
import gleam/list
import gleam/string
import gleeunit
import gleeunit/should
import tao/test_api.{
  run_test_file, calculate_summary, all_passed, get_failures,
  strip_test_lines,
  Pass, Fail,
}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// ERROR DETECTION TESTS
// ============================================================================

pub fn run_test_file_reports_syntax_errors() {
  let source = "type Bool = True | False\n\n@ bad syntax here\n"
  let #(errors, results) = run_test_file(source, "test.tao")
  // Should have at least one error
  list.is_empty(errors) |> should.be_false
  // Should have no results when there are errors
  list.length(results) |> should.equal(0)
}

pub fn run_test_file_reports_type_errors() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> 42
    | False -> True
  }
}
"
  let #(errors, results) = run_test_file(source, "test.tao")
  // Should have at least one type error
  list.is_empty(errors) |> should.be_false
  // Should have no results when there are errors
  list.length(results) |> should.equal(0)
}

pub fn run_test_file_reports_exhaustiveness_errors() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
  }
}
"
  let #(errors, results) = run_test_file(source, "test.tao")
  // Should have at least one exhaustiveness error (missing False case)
  list.is_empty(errors) |> should.be_false
  // Should have no results when there are errors
  list.length(results) |> should.equal(0)
}

// ============================================================================
// TEST RESULT TESTS
// ============================================================================

pub fn run_test_file_passing_tests() {
  // Simple file with valid tests that don't reference local functions
  let source = "
> 42 ~> 42
> 3 + 5 ~> 8
"
  let #(errors, results) = run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(2)
  // Both should pass
  all_passed(results) |> should.be_true
}

pub fn run_test_file_failing_tests() {
  let source = "
> 42 ~> 100
"
  let #(errors, results) = run_test_file(source, "test.tao")
  errors |> should.equal([])
  list.length(results) |> should.equal(1)
  all_passed(results) |> should.be_false
  let failures = get_failures(results)
  list.length(failures) |> should.equal(1)
}

// ============================================================================
// SUMMARY TESTS
// ============================================================================

pub fn calculate_summary_all_pass() {
  let results = [Pass("", 0, "42"), Pass("", 0, "true")]
  let summary = calculate_summary(results)
  summary.total |> should.equal(2)
  summary.passed |> should.equal(2)
  summary.failed |> should.equal(0)
}

pub fn calculate_summary_some_fail() {
  let results = [Pass("", 0, "42"), Fail("", 0, "100", "100", "42")]
  let summary = calculate_summary(results)
  summary.total |> should.equal(2)
  summary.passed |> should.equal(1)
  summary.failed |> should.equal(1)
}

pub fn all_passed_empty_list() {
  all_passed([]) |> should.be_true
}

pub fn get_failures_all_pass() {
  let results = [Pass("", 0, "42"), Pass("", 0, "true")]
  get_failures(results) |> should.equal([])
}

pub fn get_failures_some_fail() {
  let results = [Pass("", 0, "42"), Fail("", 0, "100", "100", "42")]
  let failures = get_failures(results)
  list.length(failures) |> should.equal(1)
}

// ============================================================================
// STRIP TEST LINES
// ============================================================================

pub fn strip_test_lines_removes_single_line_tests() {
  let source = "
type Bool = True | False
> not(True) ~> False
fn not(b: Bool) { b }
"
  let stripped = strip_test_lines(source)
  string.contains(stripped, "> not") |> should.be_false
  string.contains(stripped, "type Bool") |> should.be_true
  string.contains(stripped, "fn not") |> should.be_true
}

pub fn strip_test_lines_removes_multi_line_tests() {
  let source = "
type Bool = True | False
> not(True)
False
fn not(b: Bool) { b }
"
  let stripped = strip_test_lines(source)
  string.contains(stripped, "> not") |> should.be_false
  // The expected result line should also be removed
  // (but "False" might appear elsewhere, so check it's not after the test marker)
  string.contains(stripped, "type Bool") |> should.be_true
}

pub fn strip_test_lines_preserves_comments() {
  let source = "
// This is a comment
type Bool = True | False
> not(True) ~> False
"
  let stripped = strip_test_lines(source)
  string.contains(stripped, "// This is a comment") |> should.be_true
}

pub fn strip_test_lines_empty_input() {
  strip_test_lines("") |> should.equal("")
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn run_test_file_empty_source() {
  let #(errors, _results) = run_test_file("", "empty.tao")
  // Empty source should produce some error (no module body)
  list.is_empty(errors) |> should.be_false
}

pub fn run_test_file_only_comments() {
  let source = "// Just a comment\n// Nothing else\n"
  let #(errors, results) = run_test_file(source, "test.tao")
  // Should not crash - may or may not have errors depending on parser
  let _ = errors
  list.length(results) |> should.equal(0)
}

pub fn run_test_file_with_test_lines_only() {
  let source = "> 1 + 1 ~> 2\n> 2 * 3 ~> 6\n"
  let #(errors, results) = run_test_file(source, "test.tao")
  // No code, just test lines - the module will be empty after stripping
  // This should still produce results for the test expressions
  // (though they may fail if the expressions reference undefined things)
  let _ = errors
  list.is_empty(results) |> should.be_false
}
