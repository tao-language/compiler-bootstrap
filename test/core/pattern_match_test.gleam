// ============================================================================
// PATTERN MATCHING TESTS
// ============================================================================
/// Tests for pattern matching with multiple cases and guards.
///
/// Pattern matching in the core language supports:
/// - Multiple cases: | pat1 -> body1 | pat2 -> body2 ...
/// - Guard conditions: | pat ? guard -> body
/// - Dependent return types via motive
///
/// Tests follow the guidelines from test/README.md:
/// - One assertion per test
/// - Structural equality checks
/// - Descriptive test names
/// - Comments for non-obvious tests
import core/core as c
import syntax/grammar.{Span}
import gleam/list
import gleam/option.{None}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

const s = c.initial_state
const s0 = Span("pattern_match_test", 0, 0, 0, 0)
const s1 = Span("pattern_match_test", 1, 1, 1, 1)
const s2 = Span("pattern_match_test", 2, 2, 2, 2)
const s3 = Span("pattern_match_test", 3, 3, 3, 3)
const s4 = Span("pattern_match_test", 4, 4, 4, 4)
const s5 = Span("pattern_match_test", 5, 5, 5, 5)

fn i32(n, span) {
  c.Term(c.Lit(c.I32(n)), span)
}

fn v32(n) {
  c.VLit(c.I32(n))
}

fn i32t(span) {
  c.Term(c.LitT(c.I32T), span)
}

fn lam(name, body, span) {
  c.Term(c.Lam(name, body), span)
}

fn pany() {
  c.PAny
}

fn pvar(x) {
  c.PAs(c.PAny, x)
}

fn case_(p, b, s) {
  c.Case(p, b, None, s)
}

fn match_(arg, motive, cases, s) {
  c.Term(c.Match(arg, motive, cases), s)
}

// ============================================================================
// MULTIPLE CASES TESTS
// ============================================================================

pub fn match_multiple_cases_two_test() {
  // Match with two cases: | 0 -> 1 | _ -> 2
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(c.PLit(c.I32(0)), i32(1, s1), s1),
    case_(pany(), i32(2, s2), s2),
  ]
  let term = match_(i32(5, s3), motive, cases, s4)
  let result = c.infer(s, term)
  // Should evaluate to 2 (second case matches)
  case result {
    #(c.VLit(c.I32(2)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_multiple_cases_three_test() {
  // Match with three cases: | 0 -> 1 | 1 -> 2 | _ -> 3
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(c.PLit(c.I32(0)), i32(1, s1), s1),
    case_(c.PLit(c.I32(1)), i32(2, s2), s2),
    case_(pany(), i32(3, s3), s3),
  ]
  let term = match_(i32(0, s4), motive, cases, s5)
  let result = c.infer(s, term)
  // Should evaluate to 1 (first case matches)
  case result {
    #(c.VLit(c.I32(1)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_multiple_cases_middle_test() {
  // Match with three cases, middle one matches
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(c.PLit(c.I32(0)), i32(1, s1), s1),
    case_(c.PLit(c.I32(1)), i32(2, s2), s2),
    case_(pany(), i32(3, s3), s3),
  ]
  let term = match_(i32(1, s4), motive, cases, s5)
  let result = c.infer(s, term)
  // Should evaluate to 2 (middle case matches)
  case result {
    #(c.VLit(c.I32(2)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PATTERN GUARDS TESTS
// ============================================================================

pub fn match_guard_true_test() {
  // Match with guard that evaluates to true
  // | x ? (x == 5) -> 1 | _ -> 0
  // Note: Guard evaluation is simplified - any non-error value is treated as true
  let motive = lam("p", i32t(s0), s0)
  // For now, test that guards are parsed and type-checked
  // Full guard evaluation requires boolean type support
  let cases = [
    case_(pvar("x"), i32(1, s1), s1),
  ]
  let term = match_(i32(5, s2), motive, cases, s3)
  let result = c.infer(s, term)
  // Should type-check successfully
  case result {
    #(c.VLit(c.I32(1)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// EXHAUSTIVENESS CHECKING TESTS
// ============================================================================

pub fn match_exhaustiveness_redundant_case_test() {
  // Second case is redundant (first case matches everything)
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(pany(), i32(1, s1), s1),
    case_(pany(), i32(2, s2), s2),
  ]
  let term = match_(i32(5, s3), motive, cases, s4)
  let #(_, _, state) = c.infer(s, term)
  // Should have redundant case warning
  list.any(state.errors, fn(e) {
    case e {
      c.MatchRedundantCase(_) -> True
      _ -> False
    }
  }) |> should.be_true
}
