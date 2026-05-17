import syntax/span.{single}
/// End-to-end pipeline tests: parse -> infer -> evaluate -> quote
///
/// Covers literals, identity, let bindings, match expressions,
/// constructors, records, and error terms.

import core/ast.{type Value, VLit, Lit, Var, VCtr, VLam, VRcd, VErr, Int as LitInt, Float as LitFloat, term_to_debruijn}
import core/eval.{evaluate}
import core/infer.{infer}
import core/quote.{quote}
import core/state.{initial_state}
import core/syntax.{parse}
import gleeunit

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

/// Parse and evaluate a source string.
fn parse_eval(source: String) -> Value {
  let #(named_term, _parse_errors) = parse(source)
  let term = term_to_debruijn(named_term)
  evaluate([], [], term)
}

/// Convert an int to the corresponding literal value.
fn vi(value: Int) -> Value {
  VLit(LitInt(value))
}

// ============================================================================
// LITERAL VALUES
// ============================================================================

pub fn lit_int_42_test() {
  let quoted = quote(parse_eval("42"))
  assert case quoted {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

pub fn lit_int_zero_test() {
  let quoted = quote(parse_eval("0"))
  assert case quoted {
    Lit(LitInt(0), _) -> True
    _ -> False
  }
}

pub fn lit_float_314_test() {
  let quoted = quote(parse_eval("3.14"))
  assert case quoted {
    Lit(LitFloat(3.14), _) -> True
    _ -> False
  }
}

// ============================================================================
// IDENTITY FUNCTION
// ============================================================================

pub fn identity_type_test() {
  let value = parse_eval("$fn(x: $Int) => x")
  assert case value {
    VLam([], [], #("x", _), Var(0, _)) -> True
    _ -> False
  }
}

pub fn identity_application_test() {
  let result = parse_eval("($fn(x: $Int) => x)(42)")
  assert result == vi(42)
}

// ============================================================================
// LET BINDINGS
// ============================================================================

pub fn let_binding_test() {
  let result = parse_eval("$let x = 42; x")
  assert result == vi(42)
}

pub fn let_shadowing_test() {
  let result = parse_eval("$let x = 0; $let x = 42; x")
  assert result == vi(42)
}

// ============================================================================
// LAMBDA ABSTRACTION
// ============================================================================

pub fn lambda_unit_test() {
  let value = parse_eval("$fn(x: ()) => x")
  assert case value {
    VLam([], [], #("x", VRcd([])), Var(0, _)) -> True
    _ -> False
  }
}

pub fn nested_lambda_test() {
  let result = parse_eval("$fn(x: ()) => $fn(y: ()) => x")
  assert case result {
    VLam([], [], #("x", VRcd([])), _) -> True
    _ -> False
  }
}



// ============================================================================
// CONSTRUCTORS
// ============================================================================

pub fn constructor_some_test() {
  let result = parse_eval("#Some(42)")
  assert result == VCtr("Some", vi(42))
}

pub fn constructor_record_test() {
  let result = parse_eval("#Some({x: 42})")
  assert result == VCtr("Some", VRcd([#("x", vi(42))]))
}

// ============================================================================
// RECORDS
// ============================================================================

pub fn empty_record_test() {
  let result = parse_eval("{}")
  assert result == VRcd([])
}

pub fn single_field_record_test() {
  let result = parse_eval("{x: 1}")
  assert result == VRcd([#("x", vi(1))])
}

pub fn multi_field_record_test() {
  let result = parse_eval("{x: 1, y: 2}")
  assert result == VRcd([#("x", vi(1)), #("y", vi(2))])
}

// ============================================================================
// MATCH EXPRESSIONS
// ============================================================================

pub fn match_literal_test() {
  let result = parse_eval("$match 42 { | 0 => 1 | _ => 2 }")
  assert result == vi(2)
}

pub fn match_constructor_test() {
  let result = parse_eval(
    "$match #Some(42) { | #Some(x) => x | #None(_) => 0 }",
  )
  assert result == vi(42)
}

pub fn match_record_test() {
  let result = parse_eval(
    "$match {x: 1, y: 2} { | {x: z} => z | {} => 0 }",
  )
  assert result == vi(1)
}

// ============================================================================
// ERROR TERMS
// ============================================================================

pub fn error_term_test() {
  let result = parse_eval("$error \"my error message\"")
  assert result == VErr
}

pub fn app_to_int_test() {
  let result = parse_eval("42(1)")
  assert result == VErr
}

// ============================================================================
// INTEGRATION: TYPE CHECK + EVALUATE
// ============================================================================

pub fn pipeline_identity_test() {
  let state = initial_state([])
  let #(named_term, _) = parse("$fn(x: $Int) => x")
  let term = term_to_debruijn(named_term)
  let #(_value, _type_val, final_state) = infer(state, term)
  assert final_state.errors == []
  let evaluated = evaluate([], [], term)
  assert case evaluated {
    VLam([], [], #("x", _), _body) -> True
    _ -> False
  }
}

pub fn pipeline_lit_test() {
  let state = initial_state([])
  let #(named_term, _) = parse("42")
  let term = term_to_debruijn(named_term)
  let #(result_term, _type_val, final_state) = infer(state, term)
  assert final_state.errors == []
  assert result_term == ast.Lit(ast.Int(42), single("", 1, 1))
}

// ============================================================================
// HOLE INFERENCE
// ============================================================================

pub fn hole_untyped_let_test() {
  let result = parse_eval("$let x = 42; x")
  assert result == vi(42)
}

pub fn hole_infer_type_test() {
  let result = parse_eval("($fn(x: ?) => x)(42)")
  assert result == vi(42)
}
