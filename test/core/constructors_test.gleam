// Constructor Tests
// Tests for predefined constructors (#True, #False, #Zero, #Succ, etc.)

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
// CONSTRUCTOR TESTS
// ============================================================================

pub fn constructor_true_test() {
  // #True should be a valid constructor
  let state = infer_ok("#True")
  has_no_errors(state)
}

pub fn constructor_false_test() {
  // #False should be a valid constructor
  let state = infer_ok("#False")
  has_no_errors(state)
}

pub fn constructor_zero_test() {
  // #Zero should be a valid constructor
  let state = infer_ok("#Zero")
  has_no_errors(state)
}

pub fn constructor_succ_test() {
  // #Succ(0) should be a valid constructor application
  let state = infer_ok("#Succ(0)")
  has_no_errors(state)
}
