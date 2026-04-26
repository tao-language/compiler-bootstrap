/// Debug tests to understand parser behavior

import core/syntax
import core/ast.{Var, Lit, Int as LitInt, Rcd, Lam, Pi}

// ============================================================================
// Debug: what does the parser actually produce?
// These tests show what the parser produces for various inputs
// ============================================================================

pub fn debug_parse_fn_simple_test() {
  // Parse %fn(x: ()) => x and categorize what we get
  let #(term, errors) = syntax.parse("%fn(x: ()) => x")
  
  // Check both term type and errors - if there are errors, the test should fail
  let term_ok = case term {
    Lam(#("x", Rcd([], _)), Var(0, _), _) -> True
    _ -> False
  }
  let errors_ok = case errors {
    [] -> True
    _ -> False
  }
  
  case term_ok, errors_ok {
    True, True -> True
    _, _ -> False
  }
}

pub fn debug_parse_fn_literal_test() {
  let #(term, _errors) = syntax.parse("%fn(x: ()) => 42")
  
  case term {
    Lam(#("x", Rcd([], _)), Lit(LitInt(42), _), _) -> True
    _ -> False
  }
}

pub fn debug_parse_fn_nested_test() {
  let #(term, _errors) = syntax.parse("%fn(x: ()) => %fn(y: ()) => x")
  
  case term {
    Lam(#("x", Rcd([], _)), body, _) -> case body {
      Lam(#("y", Rcd([], _)), Var(1, _), _) -> True
      _ -> False
    }
    _ -> False
  }
}

pub fn debug_parse_fun_type_test() {
  let #(term, _errors) = syntax.parse("fun(x: ()) -> x")
  
  case term {
    Pi(Var(0, _), Var(0, _), _) -> True
    _ -> False
  }
}

pub fn debug_parse_fn_simple_errors_test() {
  let #(_, errors) = syntax.parse("%fn(x: ()) => x")
  case errors {
    [] -> True
    _ -> False
  }
}

pub fn debug_parse_lambda_with_literal_test() {
  let #(term, _errors) = syntax.parse("%fn(x: ()) => 42")
  // Check term only
  case term {
    Lam(#("x", Rcd([], _)), Lit(_, _), _) -> True
    _ -> False
  }
}
