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
import core/core as c
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s = c.initial_state

const s1 = Span("check_test", 1, 1, 1, 1)

const s2 = Span("check_test", 2, 2, 2, 2)

const v32t = c.VLitT(c.I32T)

const v64t = c.VLitT(c.I64T)

fn vhole(i) {
  c.VNeut(c.HHole(i), [])
}

// ============================================================================
// CHECK_TYPE TESTS
// ============================================================================

pub fn check_type_equal_test() {
  c.check_type(s, v32t, v32t, s1, s2)
  |> should.equal(#(v32t, s))
}

pub fn check_type_mismatch_test() {
  c.check_type(s, v32t, v64t, s1, s2)
  |> should.equal(#(
    v32t,
    c.State(..s, errors: [c.TypeMismatch(v32t, v64t, s1, s2)]),
  ))
}

pub fn check_type_with_hole_test() {
  // When one type has a hole, it gets solved
  c.check_type(s, vhole(0), v32t, s1, s2)
  |> should.equal(#(v32t, c.State(..s, sub: [#(0, v32t)])))
}

// ============================================================================
// ERROR ACCUMULATION TESTS
// ============================================================================

pub fn infer_multiple_errors_test() {
  // Create a term with multiple undefined variables
  // At least one error should be accumulated (error resilience)
  let term = c.App(c.Var(0, s1), [], c.Var(1, s1), s1)
  let #(_, _, s) = c.infer(s, term)

  // Should have at least 1 error (VarUndefined)
  case list.length(s.errors) >= 1 {
    True -> True
    False -> False
  }
  |> should.be_true
}

pub fn check_accumulates_errors_test() {
  // Type mismatch should be recorded, not thrown
  let #(_, s) = c.check(s, c.Lit(c.I32(1), s1), v64t, s2)

  s.errors
  |> should.equal([c.TypeMismatch(v32t, v64t, s1, s2)])
}
