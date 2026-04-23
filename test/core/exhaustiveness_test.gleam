// ============================================================================
// CORE EXHAUSTIVENESS TESTS
// ============================================================================
/// Tests for the exhaustiveness checker in core/exhaustiveness.gleam.
/// Verifies redundant case detection and missing case detection.
import core/ast as ast
import core/exhaustiveness as exhaustiveness
import syntax/grammar.{Span}
import gleam/list
import gleeunit
import gleeunit/should

const span = Span("exhaustiveness_test", 0, 0, 0, 0)

fn p_any() { ast.PAny(span) }
fn p_unit() { ast.PUnit(span) }
fn p_ctr(tag, inner) { ast.PCtr(tag, inner, span) }
fn p_lit(n) { ast.PLit(ast.I32(n), span) }
fn p_rcd(fields) { ast.PRcd(fields, span) }
fn p_as(inner, name) { ast.PAs(inner, name, span) }

fn make_single(p1: ast.Pattern) -> List(ast.Pattern) {
  [p1]
}

fn is_len(actual: List(a), expected: Int) -> Bool {
  case list.length(actual) == expected {
    True -> True
    False -> False
  }
}

// Temporary: verify the checker actually detects things
pub fn main() {
  gleeunit.main()
}

// Test: empty patterns -> missing case
pub fn check_empty_patterns_returns_missing_test() {
  let errors = exhaustiveness.check_exhaustiveness([], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: identical PUnit cases -> redundant
pub fn check_identical_cases_detect_redundancy_test() {
  let p1 = make_single(p_unit())
  let p2 = make_single(p_unit())
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: identical ctr patterns -> redundant
pub fn check_identical_ctr_patterns_detect_redundancy_test() {
  let p1 = make_single(p_ctr("Some", p_any()))
  let p2 = make_single(p_ctr("Some", p_any()))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: different constructors -> not redundant
pub fn check_different_constructors_not_redundant_test() {
  let p1 = make_single(p_ctr("Some", p_any()))
  let p2 = make_single(p_ctr("None", p_any()))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: wildcard makes subsequent cases redundant
pub fn check_wildcard_makes_all_redundant_test() {
  let p1 = make_single(p_any())
  let p2 = make_single(p_unit())
  let p3 = make_single(p_ctr("Some", p_any()))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2, p3], [], span)
  is_len(errors, 2) |> should.be_true
}

// Test: wildcard alone -> no missing
pub fn check_wildcard_no_missing_cases_test() {
  let p1 = make_single(p_any())
  let errors = exhaustiveness.check_exhaustiveness([p1], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: identical as-patterns -> redundant
pub fn check_identical_as_patterns_detect_redundancy_test() {
  let p1 = make_single(p_as(p_unit(), "x"))
  let p2 = make_single(p_as(p_unit(), "y"))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: different inner patterns in as-patterns -> not redundant
pub fn check_different_as_patterns_inner_not_redundant_test() {
  let p1 = make_single(p_as(p_unit(), "x"))
  let p2 = make_single(p_as(p_any(), "y"))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: identical record patterns -> redundant
pub fn check_identical_rcd_patterns_detect_redundancy_test() {
  let p1 = make_single(p_rcd([#("x", p_any())]))
  let p2 = make_single(p_rcd([#("x", p_any())]))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: different record fields -> not redundant
pub fn check_different_rcd_fields_not_redundant_test() {
  let p1 = make_single(p_rcd([#("x", p_any())]))
  let p2 = make_single(p_rcd([#("y", p_any())]))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: same fields but different inner -> not redundant
pub fn check_same_rcd_fields_different_inner_not_redundant_test() {
  let p1 = make_single(p_rcd([#("x", p_unit())]))
  let p2 = make_single(p_rcd([#("x", p_any())]))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: only literal patterns -> missing
pub fn check_only_literal_patterns_detects_missing_test() {
  let p1 = make_single(p_lit(1))
  let errors = exhaustiveness.check_exhaustiveness([p1], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: multiple literals without wildcard -> missing
pub fn check_multiple_literals_detects_missing_test() {
  let p1 = make_single(p_lit(1))
  let p2 = make_single(p_lit(2))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: literal + wildcard -> no missing
pub fn check_literal_and_wildcard_no_missing_test() {
  let p1 = make_single(p_lit(1))
  let p2 = make_single(p_any())
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: constructor without wildcard -> not detected as incomplete
/// (the checker doesn't track which constructors exist per type)
pub fn check_constructor_patterns_not_detected_as_missing_test() {
  let p1 = make_single(p_ctr("Some", p_any()))
  let errors = exhaustiveness.check_exhaustiveness([p1], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: partial constructor coverage -> not detected as incomplete
/// (the checker doesn't track which constructors exist per type)
pub fn check_partial_constructor_coverage_not_detected_as_missing_test() {
  let p1 = make_single(p_ctr("Some", p_any()))
  let p2 = make_single(p_ctr("True", p_any()))
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 0) |> should.be_true
}

// Test: mixed redundant and missing
pub fn check_mixed_redundant_and_missing_test() {
  let p1 = make_single(p_unit())
  let p2 = make_single(p_any())
  let p3 = make_single(p_unit())
  let errors = exhaustiveness.check_exhaustiveness([p1, p2, p3], [], span)
  is_len(errors, 1) |> should.be_true
}

// Test: multi-pattern rows
pub fn check_multi_pattern_rows_test() {
  let p1 = [p_any(), p_unit()]
  let p2 = [p_ctr("Some", p_any()), p_any()]
  let errors = exhaustiveness.check_exhaustiveness([p1, p2], [], span)
  is_len(errors, 1) |> should.be_true
}
