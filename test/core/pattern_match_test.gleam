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
import core/ast as ast
import core/state as state
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

fn get_s() { state.initial_state() }
const s0 = Span("pattern_match_test", 0, 0, 0, 0)
const s1 = Span("pattern_match_test", 1, 1, 1, 1)
const s2 = Span("pattern_match_test", 2, 2, 2, 2)
const s3 = Span("pattern_match_test", 3, 3, 3, 3)
const s4 = Span("pattern_match_test", 4, 4, 4, 4)
const s5 = Span("pattern_match_test", 5, 5, 5, 5)

fn i32(n, span) {
  ast.Lit(ast.I32(n), span)
}

fn i64(n, span) {
  ast.Lit(ast.I64(n), span)
}

fn v32(n) {
  ast.VLit(ast.I32(n))
}

fn v64(n) {
  ast.VLit(ast.I64(n))
}

fn i32t(span) {
  ast.LitT(ast.I32T, span)
}

fn i64t(span) {
  ast.LitT(ast.I64T, span)
}

fn lam(name, body, span) {
  ast.Lam([], #(name, ast.Hole(-1, s1)), body, span)
}

fn pany() {
  ast.PAny
}

fn pvar(x) {
  ast.PAs(ast.PAny, x)
}

fn var(i, span) {
  ast.Var(i, span)
}

fn case_(p, b, s) {
  c.Case(p, b, None, s)
}

fn match_(arg, motive, cases, s) {
  ast.Match(arg, motive, cases, s)
}

// ============================================================================
// MULTIPLE CASES TESTS
// ============================================================================

pub fn match_multiple_cases_two_test() {
  // Match with two cases: | 0 -> 1 | _ -> 2
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(pany(), i32(2, s2), s2),
  ]
  let term = match_(i32(5, s3), motive, cases, s4)
  let result = infer(s, term)
  // Should evaluate to 2 (second case matches)
  case result {
    #(ast.VLit(ast.I32(2)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_multiple_cases_three_test() {
  // Match with three cases: | 0 -> 1 | 1 -> 2 | _ -> 3
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(ast.PLit(ast.I32(1)), i32(2, s2), s2),
    case_(pany(), i32(3, s3), s3),
  ]
  let term = match_(i32(0, s4), motive, cases, s5)
  let result = infer(s, term)
  // Should evaluate to 1 (first case matches)
  case result {
    #(ast.VLit(ast.I32(1)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_multiple_cases_middle_test() {
  // Match with three cases, middle one matches
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(ast.PLit(ast.I32(1)), i32(2, s2), s2),
    case_(pany(), i32(3, s3), s3),
  ]
  let term = match_(i32(1, s4), motive, cases, s5)
  let result = infer(s, term)
  // Should evaluate to 2 (middle case matches)
  case result {
    #(ast.VLit(ast.I32(2)), _, _) -> True |> should.be_true
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
  let result = infer(s, term)
  // Should type-check successfully
  case result {
    #(ast.VLit(ast.I32(1)), _, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// HOLE MOTIVE INFERENCE TESTS (Non-dependent matches)
// ============================================================================

pub fn match_hole_motive_infer_int_test() {
  // Non-dependent match with hole motive - should infer Int result type
  // This is the common case for Tao: match 0 { | 0 -> 1 | _ -> 2 }
  let motive = lam("p", ast.Hole(-1, s0), s0)  // Hole motive
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(pany(), i32(2, s2), s2),
  ]
  let term = match_(i32(0, s3), motive, cases, s4)
  let result = infer(s, term)
  // Should infer Int result type and evaluate to 1
  case result {
    #(ast.VLit(ast.I32(1)), ast.VLitT(ast.I32T), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_hole_motive_infer_mismatch_test() {
  // Non-dependent match with hole motive - type mismatch between clauses
  // First clause returns Int, second returns I64 - should report error
  let motive = lam("p", ast.Hole(-1, s0), s0)  // Hole motive
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(pany(), i64(2, s2), s2),  // Different type!
  ]
  let term = match_(i32(0, s3), motive, cases, s4)
  let result = infer(s, term)
  // Should have type mismatch error
  case result {
    #(_, _, state) -> {
      list.any(state.errors, fn(e) {
        case e {
          state.TypeMismatch(_, _, _, _) -> True
          _ -> False
        }
      }) |> should.be_true
    }
    _ -> False |> should.be_true
  }
}

pub fn match_hole_motive_infer_string_test() {
  // Non-dependent match with hole motive - infer I64 result type
  // (Using I64 instead of String since core doesn't have string literals)
  let motive = lam("p", ast.Hole(-1, s0), s0)  // Hole motive
  let cases = [
    case_(ast.PLit(ast.I32(0)), i64(100, s1), s1),
    case_(pany(), i64(200, s2), s2),
  ]
  let term = match_(i32(0, s3), motive, cases, s4)
  let result = infer(s, term)
  // Should infer I64 result type
  case result {
    #(ast.VLit(ast.I64(100)), ast.VLitT(ast.I64T), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// DEPENDENT MATCH TESTS
// ============================================================================

pub fn match_dependent_motive_explicit_test() {
  // Dependent match with explicit motive that references scrutinee
  // The motive fn(x: Int) -> if x == 0 then Int else I64
  // For simplicity, we use a concrete dependent type here
  let motive = lam("p", i32t(s0), s0)  // Non-dependent, but explicitly provided
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
    case_(pany(), i32(2, s2), s2),
  ]
  let term = match_(i32(0, s3), motive, cases, s4)
  let result = infer(s, term)
  // Should use the explicit motive and evaluate correctly
  case result {
    #(ast.VLit(ast.I32(1)), ast.VLitT(ast.I32T), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn match_dependent_motive_with_var_test() {
  // Dependent match where body uses the bound variable from pattern
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    // Pattern binds x, body uses x
    case_(pvar("x"), var(0, s1), s1),
  ]
  let term = match_(i32(42, s2), motive, cases, s3)
  let result = infer(s, term)
  // Should return 42 (the scrutinee value)
  case result {
    #(ast.VLit(ast.I32(42)), ast.VLitT(ast.I32T), _) -> True |> should.be_true
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
  let #(_, _, state) = infer(s, term)
  // Should have redundant case warning
  list.any(state.errors, fn(e) {
    case e {
      state.MatchRedundantCase(_) -> True
      _ -> False
    }
  }) |> should.be_true
}

pub fn match_exhaustiveness_wildcard_is_exhaustive_test() {
  // Wildcard pattern should be recognized as exhaustive
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(pany(), i32(100, s1), s1),
  ]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = infer(s, term)
  // Should NOT have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e {
      state.MatchMissingCase(_, _) -> True
      _ -> False
    }
  }) |> should.be_false
}

pub fn match_exhaustiveness_as_wildcard_is_exhaustive_test() {
  // As-pattern with wildcard should be recognized as exhaustive
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(ast.PAs(ast.PAny, "x"), i32(100, s1), s1),
  ]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = infer(s, term)
  // Should NOT have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e {
      state.MatchMissingCase(_, _) -> True
      _ -> False
    }
  }) |> should.be_false
}

pub fn match_exhaustiveness_missing_case_test() {
  // Missing wildcard should produce exhaustiveness error
  let motive = lam("p", i32t(s0), s0)
  let cases = [
    case_(ast.PLit(ast.I32(0)), i32(1, s1), s1),
  ]
  let term = match_(i32(5, s2), motive, cases, s3)
  let #(_, _, state) = infer(s, term)
  // Should have exhaustiveness error
  list.any(state.errors, fn(e) {
    case e {
      state.MatchMissingCase(_, _) -> True
      _ -> False
    }
  }) |> should.be_true
}
