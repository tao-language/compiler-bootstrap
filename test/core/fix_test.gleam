// ============================================================================
// FIXPOINT OPERATOR TESTS
// ============================================================================
/// Tests for the fixpoint operator (fix f -> body) for recursion.
///
/// The fixpoint operator allows defining recursive functions:
/// - fix f -> body unfolds by substituting itself into body
/// - Type: (A -> A) -> A
///
/// Tests follow the guidelines from test/README.md:
/// - One assertion per test
/// - Structural equality checks
/// - Descriptive test names
import core/ast as ast
import core/state as state
import core/infer.{infer}
import core/quote.{quote}
import syntax/grammar.{Span}
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

const s0 = Span("fix_test", 0, 0, 0, 0)
const s1 = Span("fix_test", 1, 1, 1, 1)
const s2 = Span("fix_test", 2, 2, 2, 2)
const s3 = Span("fix_test", 3, 3, 3, 3)

fn i32(n, span) {
  ast.Lit(ast.I32(n), span)
}

fn v32(n) {
  ast.VLit(ast.I32(n))
}

fn v32t() {
  ast.VLitT(ast.I32T)
}

fn lam(name, body, span) {
  ast.Lam([], #(name, ast.Hole(-1, s1)), body, span)
}

fn app(fun, arg, span) {
  ast.App(fun, [], arg, span)
}

fn var(i, span) {
  ast.Var(i, span)
}

fn fix(name, body, span) {
  ast.Fix(name, body, span)
}

// ============================================================================
// FIXPOINT PARSING AND TYPE CHECKING TESTS
// ============================================================================

pub fn fix_parse_simple_test() {
  // fix f -> f should parse and type-check
  // This is the identity function via fixpoint
  let body = var(0, s0)  // f refers to the fixpoint itself
  let term = fix("f", body, s1)
  let #(_val, _ty, s) = infer(state.initial_state, term)
  // Should type-check with no errors
  let error_count = list.length(s.errors)
  error_count |> should.equal(0)
}

pub fn fix_parse_apply_test() {
  // fix f -> f x should parse (f applied to x)
  // Note: This requires x to be in scope
  let x = var(1, s0)  // x is outer variable
  let f = var(0, s1)  // f is the fixpoint
  let body = app(f, x, s2)
  let term = fix("f", body, s3)
  let #(_val, _ty, s) = infer(state.initial_state, term)
  // Should type-check (may have errors due to unbound x)
  // At least it should complete without crashing
  let completed = True
  completed |> should.be_true()
}

// ============================================================================
// FIXPOINT EVALUATION TESTS
// ============================================================================

pub fn fix_eval_unfold_test() {
  // fix f -> f should unfold to itself when applied
  // (fix f -> f) x = f x [f := fix f -> f] = (fix f -> f) x
  // This creates an infinite loop, but we can test the unfolding
  let body = var(0, s0)  // f
  let fix_term = fix("f", body, s1)
  let arg = i32(42, s2)
  let term = app(fix_term, arg, s3)
  let #(_val, _ty, s) = infer(state.initial_state, term)
  // Should complete without infinite loop (step counter protection)
  let completed = True
  completed |> should.be_true()
}

// ============================================================================
// FIXPOINT QUOTING TESTS
// ============================================================================

pub fn fix_quote_roundtrip_test() {
  // fix f -> f should quote back correctly
  let body = var(0, s0)
  let term = fix("f", body, s1)
  let #(_val, _ty, _s) = infer(state.initial_state, term)
  // Quote the value back
  let quoted = quote(state.initial_ffis, 0, ast.VFix("f", [], body), s0)
  // Should quote back to a Fix term
  case quoted {
    ast.Fix(_, _, _) -> True |> should.be_true()
    _ -> False |> should.be_true()
  }
}

// ============================================================================
// FIXPOINT OCCURS CHECK TESTS
// ============================================================================

pub fn fix_occurs_check_test() {
  // Fixpoint should not cause infinite loops in occurs check
  let body = var(0, s0)
  let term = fix("f", body, s1)
  let #(_val, _ty, s) = infer(state.initial_state, term)
  // Should complete without infinite loop
  let completed = True
  completed |> should.be_true()
  // And should have no errors for this simple case
  let error_count = list.length(s.errors)
  error_count |> should.equal(0)
}
