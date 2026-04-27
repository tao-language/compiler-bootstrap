/// Tests for the Infer module (Bidirectional Type Checking)
///
/// Tests cover:
/// - Literal inference (int, float)
/// - Type universe inference
/// - Variable inference (in scope, out of scope)
/// - Hole inference
/// - Lambda inference
/// - Pi type inference
/// - Application inference
/// - Annotation inference
/// - Record inference
/// - Constructor inference
/// - Error term inference
/// - Check function (infer + unify)

import core/ast.{
  type Term, type Value,
  Ann, App, Ctr, Err, Hole, HHole, HVar, Lam, Lit, Pi, Rcd, Typ,
  VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, Var,
  Int as LitInt, Float as LitFloat,
}
import core/infer.{check, infer}
import core/state.{initial_state, State}
import gleeunit
import syntax/span.{single, type Span}
import core/eval.{evaluate}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

fn sp() -> Span {
  single("infer_test", 0, 0)
}

fn lit_int(v: Int) -> Term {
  Lit(LitInt(v), sp())
}

fn lit_float(v: Float) -> Term {
  Lit(LitFloat(v), sp())
}

fn var(i: Int) -> Term {
  Var(i, sp())
}

fn hole(id: Int) -> Term {
  Hole(id, sp())
}

fn typ(lvl: Int) -> Term {
  Typ(lvl, sp())
}

fn lam(param_name: String, param_type: Term, body: Term) -> Term {
  Lam(#(param_name, param_type), body, sp())
}

fn pi(domain: Term, codomain: Term) -> Term {
  Pi(domain, codomain, sp())
}

fn app(fun: Term, arg: Term) -> Term {
  App(fun, arg, sp())
}

fn ann(inner: Term, type_: Term) -> Term {
  Ann(inner, type_, sp())
}

fn rcd(fields: List(#(String, Term))) -> Term {
  Rcd(fields, sp())
}

fn ctr(tag: String, arg: Term) -> Term {
  Ctr(tag, arg, sp())
}

fn err() -> Term {
  Err("error", sp())
}

fn v_int(v: Int) -> Value {
  VLit(LitInt(v))
}

fn v_neut(level: Int) -> Value {
  VNeut(HVar(level), [])
}

// ============================================================================
// LITERAL INFERENCE
// ============================================================================

pub fn infer_lit_int_test() {
  let result = infer(initial_state([]), lit_int(42))
  let #(value, type_, _) = result
  assert value == v_int(42)
  assert type_ == v_int(42)
}

pub fn infer_lit_int_zero_test() {
  let result = infer(initial_state([]), lit_int(0))
  let #(value, type_, _) = result
  assert value == v_int(0)
  assert type_ == v_int(0)
}

pub fn infer_lit_int_negative_test() {
  let result = infer(initial_state([]), lit_int(-1))
  let #(value, type_, _) = result
  assert value == v_int(-1)
  assert type_ == v_int(-1)
}

pub fn infer_lit_float_test() {
  let result = infer(initial_state([]), lit_float(3.14))
  let #(value, type_, _) = result
  assert value == VLit(LitFloat(3.14))
  assert type_ == VLit(LitFloat(3.14))
}

// ============================================================================
// TYPE UNIVERSE INFERENCE
// ============================================================================

pub fn infer_typ_level_zero_test() {
  let result = infer(initial_state([]), typ(0))
  let #(value, type_, _) = result
  assert value == v_neut(0)
  assert type_ == v_neut(1)
}

pub fn infer_typ_level_one_test() {
  let result = infer(initial_state([]), typ(1))
  let #(value, type_, _) = result
  assert value == v_neut(1)
  assert type_ == v_neut(2)
}

// ============================================================================
// VARIABLE INFERENCE
// ============================================================================

pub fn infer_var_in_scope_test() {
  let x_val: Value = VLit(LitInt(42))
  let x_type: Value = v_int(42)
  let state = State(
    ..initial_state([]),
    vars: [#("x", #(x_val, x_type))],
  )
  let result = infer(state, var(0))
  let #(value, type_, _) = result
  assert value == x_val
  assert type_ == x_type
}

pub fn infer_var_out_of_scope_test() {
  let result = infer(initial_state([]), var(0))
  let #(value, type_, _state) = result
  assert value == VErr
  assert type_ == VErr
  let result2 = infer(initial_state([]), var(0))
  let has_error = result2.2.errors != []
  assert has_error
}

// ============================================================================
// HOLE INFERENCE
// ============================================================================

pub fn infer_hole_test() {
  let result = infer(initial_state([]), hole(0))
  let #(value, type_, state) = result
  assert case value {
    VNeut(..) -> True
    _ -> False
  }
  assert type_ == value
  assert state.hole_counter == 1
}

pub fn infer_hole_incremental_test() {
  let state = State(..initial_state([]), hole_counter: 5)
  let result = infer(state, hole(0))
  let #(value, _, state2) = result
  assert state2.hole_counter == 6
  assert case value {
    VNeut(HHole(5), []) -> True
    _ -> False
  }
}

// ============================================================================
// LAMBDA INFERENCE
// ============================================================================

pub fn infer_lambda_identity_test() {
  // fn(x: Int) -> x : Π(Int) -> Int
  let param_type = lit_int(0)
  let body = var(0)
  let lam = lam("x", param_type, body)
  let result = infer(initial_state([]), lam)
  let #(value, type_, _) = result
  assert case value {
    VLam(#("x", _), _) -> True
    _ -> False
  }
  assert case type_ {
    VPi(_, _) -> True
    _ -> False
  }
}

pub fn infer_lambda_constant_test() {
  // fn(x: Int) -> 42 : Π(Int) -> Int
  let param_type = lit_int(0)
  let body = lit_int(42)
  let lam = lam("x", param_type, body)
  let result = infer(initial_state([]), lam)
  let #(value, type_, _) = result
  assert case value {
    VLam(..) -> True
    _ -> False
  }
  assert case type_ {
    VPi(_, _) -> True
    _ -> False
  }
}

// ============================================================================
// PI TYPE INFERENCE
// ============================================================================

pub fn infer_pi_type_test() {
  // Π(x: Int) -> Int
  let domain = lit_int(0)
  let codomain = lit_int(0)
  let pi = pi(domain, codomain)
  let result = infer(initial_state([]), pi)
  let #(value, type_, _) = result
  assert case value {
    VPi(_, _) -> True
    _ -> False
  }
  assert type_ == v_neut(0)
}

// ============================================================================
// APPLICATION INFERENCE
// ============================================================================

pub fn infer_app_not_a_function_test() {
  // 42 42 : should error
  let result = infer(initial_state([]), app(lit_int(42), lit_int(0)))
  let #(value, type_, _state) = result
  assert value == VErr
  assert type_ == VErr
  let result2 = infer(initial_state([]), var(0))
  let has_error = result2.2.errors != []
  assert has_error
}

// ============================================================================
// ANNOTATION INFERENCE
// ============================================================================

pub fn infer_ann_same_type_test() {
  // 42 : Int → Int
  let inner = lit_int(42)
  let type_ = lit_int(42)
  let ann_term = ann(inner, type_)
  let result = infer(initial_state([]), ann_term)
  let #(value, type_ret, _) = result
  assert value == v_int(42)
  assert type_ret == v_int(42)
}

pub fn infer_ann_nested_test() {
  // (42 : Int) : Int → Int
  let inner = lit_int(42)
  let type_1 = lit_int(42)
  let inner_ann = ann(inner, type_1)
  let type_2 = lit_int(42)
  let outer_ann = ann(inner_ann, type_2)
  let result = infer(initial_state([]), outer_ann)
  let #(value, type_ret, _) = result
  assert value == v_int(42)
  assert type_ret == v_int(42)
}

// ============================================================================
// RECORD INFERENCE
// ============================================================================

pub fn infer_rcd_empty_test() {
  let result = infer(initial_state([]), rcd([]))
  let #(value, type_, _) = result
  assert value == VRcd([])
  assert type_ == v_neut(0)
}

pub fn infer_rcd_single_field_test() {
  let result = infer(
    initial_state([]),
    rcd([#("x", lit_int(42))]),
  )
  let #(value, type_, _) = result
  assert case value {
    VRcd([#("x", VLit(LitInt(42)))] ) -> True
    _ -> False
  }
  assert type_ == v_neut(0)
}

pub fn infer_rcd_multiple_fields_test() {
  let result = infer(
    initial_state([]),
    rcd([#("a", lit_int(1)), #("b", lit_int(2))]),
  )
  let #(value, type_, _) = result
  assert case value {
    VRcd([#("a", VLit(LitInt(1))), #("b", VLit(LitInt(2)))] ) -> True
    _ -> False
  }
  assert type_ == v_neut(0)
}

// ============================================================================
// CONSTRUCTOR INFERENCE
// ============================================================================

pub fn infer_ctr_simple_test() {
  let result = infer(initial_state([]), ctr("Just", lit_int(42)))
  let #(value, type_, _) = result
  assert case value {
    VCtr("Just", VLit(LitInt(42))) -> True
    _ -> False
  }
  assert type_ == v_neut(0)
}

pub fn infer_ctr_nested_test() {
  let nested = ctr("fst", lit_int(1))
  let result = infer(
    initial_state([]),
    ctr("Pair", nested),
  )
  let #(value, _, _) = result
  assert case value {
    VCtr("Pair", VCtr("fst", VLit(LitInt(1)))) -> True
    _ -> False
  }
}

// ============================================================================
// ERROR TERM INFERENCE
// ============================================================================

pub fn infer_err_test() {
  let result = infer(initial_state([]), err())
  let #(value, type_, _) = result
  assert value == VErr
  assert type_ == VErr
}

// ============================================================================
// CHECK FUNCTION TESTS
// ============================================================================

pub fn check_lit_int_matches_test() {
  // Check that 42 has type "42" (same literal)
  let term = lit_int(42)
  let term_type: Value = v_int(42)
  let result = check(initial_state([]), term, term_type)
  let #(value, type_, _) = result
  assert value == v_int(42)
  assert type_ == v_int(42)
}

pub fn check_nested_same_type_test() {
  // Check (42 : Int) : Int → Int
  let inner = ann(lit_int(42), lit_int(42))
  let expected_type: Value = v_int(42)
  let result = check(initial_state([]), inner, expected_type)
  let #(value, type_, _) = result
  assert value == v_int(42)
  assert type_ == v_int(42)
}

// ============================================================================
// PROPERTY: EVALUATE → INFER → FORCE ROUND-TRIP
// ============================================================================

pub fn infer_roundtrip_lit_int_test() {
  // Evaluate a literal, then infer its type
  let term = lit_int(42)
  let state = initial_state([])
  let evaluated = evaluate(state, term)
  let result = infer(state, term)
  let #(value, _, _) = result
  // Both should produce the same value
  assert case evaluated {
    VLit(LitInt(42)) -> True
    _ -> False
  }
  assert value == v_int(42)
}

pub fn infer_roundtrip_lit_float_test() {
  let term = lit_float(1.0)
  let state = initial_state([])
  let evaluated = evaluate(state, term)
  let result = infer(state, term)
  let #(value, _, _) = result
  assert case evaluated {
    VLit(LitFloat(1.0)) -> True
    _ -> False
  }
  assert value == VLit(LitFloat(1.0))
}

pub fn infer_roundtrip_lambda_test() {
  // Lambda evaluates to a VLam
  let lam = lam("x", lit_int(0), var(0))
  let state = initial_state([])
  let evaluated = evaluate(state, lam)
  let result = infer(state, lam)
  let #(value, type_, _) = result
  assert case evaluated {
    VLam(..) -> True
    _ -> False
  }
  assert case value {
    VLam(..) -> True
    _ -> False
  }
  assert case type_ {
    VPi(_, _) -> True
    _ -> False
  }
}

// ============================================================================
// DEBUG TESTS — Simplified
// ============================================================================

pub fn debug_simple_lit_test() {
  // Just test that a literal infers correctly
  let result = infer(initial_state([]), lit_int(0))
  let #(value, type_, _) = result
  assert value == v_int(0)
  assert type_ == v_int(0)
}

pub fn debug_lam_test() {
  // Test lambda inference alone
  let lam = lam("x", lit_int(0), var(0))
  let result = infer(initial_state([]), lam)
  let #(value, type_, _) = result
  assert case value {
    VLam(..) -> True
    _ -> False
  }
  assert case type_ {
    VPi(..) -> True
    _ -> False
  }
}
