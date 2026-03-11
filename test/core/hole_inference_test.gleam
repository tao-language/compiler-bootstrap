// Hole Inference Tests
// Tests for the hole inference feature that allows holes to expand in application context

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
// HOLE INFERENCE TESTS
// ============================================================================

pub fn hole_inference_let_function_test() {
  // let id = x -> x in id(42) should infer id's type as a function
  let state = infer_ok("let id = x -> x in id(42)")
  has_no_errors(state)
}

pub fn hole_inference_nested_application_test() {
  // let f = x -> y -> x in f(1)(2) should infer f's type
  let state = infer_ok("let f = x -> y -> x in f(1)(2)")
  has_no_errors(state)
}

pub fn hole_inference_simple_application_test() {
  // (x -> x)(42) should work
  let state = infer_ok("(x -> x)(42)")
  has_no_errors(state)
}

pub fn hole_inference_curried_test() {
  // let add = x -> y -> x in add(10)(20)
  let state = infer_ok("let add = x -> y -> x in add(10)(20)")
  has_no_errors(state)
}
