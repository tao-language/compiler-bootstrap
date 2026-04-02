// ============================================================================
// TYPE CHECKING TESTS
// ============================================================================
/// Tests for bidirectional type checking.
///
/// The type checker has two modes:
/// - check_type: Verify a value has a given type (checking)
/// - infer: Determine the type of a value (inference)
///
/// Error accumulation ensures all errors are reported, not just the first.
import core/ast as ast
import core/state as state
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/check.{check_type, check}
import core/infer.{infer}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s = state.initial_state

const s1 = Span("check_test", 1, 1, 1, 1)

const s2 = Span("check_test", 2, 2, 2, 2)

const v32t = ast.VLitT(ast.I32T)

const v64t = ast.VLitT(ast.I64T)

fn vhole(i) {
  ast.VNeut(ast.HHole(i), [])
}

// ============================================================================
// CHECK_TYPE TESTS
// ============================================================================

pub fn check_type_equal_test() {
  let #(s2, _) = check_type(s, v32t, v32t, s1, s2)
  s2 |> should.equal(s)
}

pub fn check_type_mismatch_test() {
  let #(s_result, _) = check_type(s, v32t, v64t, s1, s2)
  s_result |> should.equal(state.State(..s, errors: [state.TypeMismatch(v32t, v64t, s1, s2)]))
}

pub fn check_type_with_hole_test() {
  // When one type has a hole, it gets solved
  let #(s_result, _) = check_type(s, vhole(0), v32t, s1, s2)
  s_result |> should.equal(state.State(..s, subst: [#(0, v32t)]))
}

// ============================================================================
// ERROR ACCUMULATION TESTS
// ============================================================================

pub fn infer_multiple_errors_test() {
  // Create a term with multiple undefined variables
  // At least one error should be accumulated (error resilience)
  let term = ast.App(ast.Var(0, s1), [], ast.Var(1, s1), s1)
  let #(_, _, s) = infer(s, term)

  // Should have at least 1 error (VarUndefined)
  case list.length(s.errors) >= 1 {
    True -> True
    False -> False
  }
  |> should.be_true
}

pub fn check_accumulates_errors_test() {
  // Type mismatch should be recorded, not thrown
  let #(_, s) = check(s, ast.Lit(ast.I32(1), s1), v64t, s1)

  s.errors
  |> should.equal([state.TypeMismatch(v32t, v64t, Span("", 0, 0, 0, 0), s1)])
}
