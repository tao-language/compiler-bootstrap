// Vector Tests
// Tests for length-indexed vectors

import gleeunit
import gleeunit/should
import core/core.{type State, initial_state, infer}
import core/syntax.{parse}
import syntax/grammar.{ParseResult}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn infer_ok(source: String) -> State {
  let ParseResult(term, errors) = parse(source)
  case errors {
    [] -> {
      let #(_val, _ty, state) = infer(initial_state, term)
      state
    }
    [_err, ..] -> {
      panic as "Parse failed"
    }
  }
}

fn has_no_errors(state: State) {
  case state.errors {
    [] -> Nil
    [_err, ..] -> {
      panic as "Expected no errors"
    }
  }
}

// ============================================================================
// VECTOR TESTS
// ============================================================================

pub fn vector_vnil_test() {
  // #VNil should be a valid constructor
  let state = infer_ok("#VNil")
  has_no_errors(state)
}

pub fn vector_vcons_test() {
  // #VCons with element and tail should work
  let state = infer_ok("#VCons(1, #VNil)")
  has_no_errors(state)
}

pub fn vector_nested_test() {
  // Nested VCons should work
  let state = infer_ok("#VCons(1, #VCons(2, #VNil))")
  has_no_errors(state)
}

pub fn vector_nat_zero_test() {
  // #Zero should work as length index
  let state = infer_ok("#Zero")
  has_no_errors(state)
}

pub fn vector_nat_succ_test() {
  // #Succ should work
  let state = infer_ok("#Succ(#Zero)")
  has_no_errors(state)
}
