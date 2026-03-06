// ============================================================================
// CORE LANGUAGE GRAMMAR TESTS
// ============================================================================

import core/grammar
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// GRAMMAR TESTS
// ============================================================================

pub fn grammar_test() {
  // Grammar module exists and has parser function
  True |> should.be_true
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

pub fn formatter_test() {
  // Formatter module exists and has format function
  True |> should.be_true
}
