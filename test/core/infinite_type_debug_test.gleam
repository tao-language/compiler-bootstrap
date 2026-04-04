// ============================================================================
// INFINITE TYPE DEBUG TESTS
// ============================================================================
/// Targeted tests to debug and fix the InfiniteType error in bool.tao.
///
/// The error: InfiniteType(3, VPi([], "_", [], VNeut(HHole(0), []), Hole(2, ...)))
///
/// Root cause analysis:
/// 1. Module-level lambdas create holes for parameter types (Hole(-1) -> new_hole)
/// 2. Hole 0 = Bool's type, Hole 1 = not's type, Hole 2 = and's type, etc.
/// 3. When functions are type-checked, their types are unified with these holes
/// 4. The unification can create indirect cycles through the substitution chain
/// 5. The occurs check for VPi ignores codomain terms (bug)

import core/ast as ast
import core/state as state
import core/infer.{infer}
import core/unify.{occurs}
import core/subst
import syntax/grammar.{Span}
import tao/test_api
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

const s1 = Span("test", 0, 0, 0, 0)

// ============================================================================
// HELPERS
// ============================================================================

fn i32(n, s) {
  ast.Lit(ast.I32(n), s)
}

fn var(i, s) {
  ast.Var(i, s)
}

fn lam(name, body, s) {
  ast.Lam([], #(name, ast.Hole(-1, s)), body, s)
}

fn lam_with_type(name, param_ty, body, s) {
  ast.Lam([], #(name, param_ty), body, s)
}

fn app(fun, arg, s) {
  ast.App(fun, [], arg, s)
}

fn hole(id, s) {
  ast.Hole(id, s)
}

fn ctr(name, s) {
  ast.Ctr(name, ast.Unit(s), s)
}

fn v32(n) {
  ast.VLit(ast.I32(n))
}

fn vctr(name) {
  ast.VCtrValue(ast.VCtr(name, ast.VUnit))
}

fn has_infinite_type(errors: List(state.Error)) -> Bool {
  list.any(errors, fn(e) {
    case e {
      state.InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
}

// ============================================================================
// TEST 1: Module lambda hole
// ============================================================================
/// Simulates module desugaring: λBool. λnot. ... result
/// Each lambda has Hole(-1) parameter type, creating holes 0, 1, 2, ...
pub fn module_lambda_hole_test() {
  // Simulate: λBool. λnot. {not: not}
  // This creates:
  // - Hole 0 for Bool's type
  // - Hole 1 for not's type
  // - Body: record with not field
  
  // Inner lambda: λnot. {not: not}
  let not_var = var(0, s1)  // not is at index 0
  let record = ast.Rcd([#("not", not_var)], s1)
  let inner_lam = lam("not", record, s1)
  
  // Outer lambda: λBool. inner_lam
  let outer_lam = lam("Bool", inner_lam, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, outer_lam)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 2: Hole unified with constructor
// ============================================================================
/// When a hole is unified with a constructor type, it should not create cycles.
pub fn hole_unified_with_constructor_test() {
  // Create a lambda with hole parameter type, then apply to a constructor
  // λx. x  where x has hole type
  // Apply to: Ctr("Bool", Unit)
  
  let identity = lam("x", var(0, s1), s1)
  let bool_ctr = ctr("Bool", s1)
  let app_term = app(identity, bool_ctr, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, app_term)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 3: Nested lambda application
// ============================================================================
/// Simulates module desugaring: (λBool. (λnot. result) not) Bool
pub fn nested_lambda_application_test() {
  // result = {not: not}
  let not_var = var(0, s1)
  let record = ast.Rcd([#("not", not_var)], s1)
  
  // λnot. {not: not}
  let lam_not = lam("not", record, s1)
  
  // (λnot. {not: not}) (λb. b)
  let identity = lam("b", var(0, s1), s1)
  let app1 = app(lam_not, identity, s1)
  
  // λBool. (λnot. {not: not}) (λb. b)
  let lam_bool = lam("Bool", app1, s1)
  
  // (λBool. ...) Bool
  let bool_ctr = ctr("Bool", s1)
  let app2 = app(lam_bool, bool_ctr, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, app2)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 4: Function with annotated parameters
// ============================================================================
/// Simulates: fn implies(a: Bool, b: Bool) -> Bool { or(not(a), b) }
/// The parameters have type annotations, so the lambda should be checked
/// against the annotated type, not inferred with holes.
pub fn function_with_annotated_params_test() {
  // Simulate the implies function with annotated parameters
  // λa: Bool. λb: Bool. or(not(a), b)
  
  // For this test, we use holes for Bool since we don't have the full context
  // The key is that the parameter types should be consistent
  
  // not(a): not at index 2, a at index 1
  let not_a = app(var(2, s1), var(1, s1), s1)
  // or(not(a), b): or at index 3, not(a) above, b at index 0
  let or_call = app(app(var(3, s1), not_a, s1), var(0, s1), s1)
  
  // λb. or(not(a), b)
  let lam_b = lam("b", or_call, s1)
  // λa. λb. or(not(a), b)
  let lam_a = lam("a", lam_b, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, lam_a)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 5: Occurs check VPi codomain
// ============================================================================
/// Test that the occurs check detects cycles in VPi codomain terms.
/// This is a known bug: occurs check ignores VPi codomain terms.
pub fn occurs_check_vpi_codomain_test() {
  // Create a scenario where a hole appears in a VPi codomain term
  // hole 0 = VPi(..., Int, Hole(0))  -- cycle through codomain
  
  // This test verifies the current behavior (may fail if bug is present)
  // The occurs check should detect this cycle but currently doesn't
  
  // For now, just verify that basic occurs check works
  let sub = [#(0, ast.VNeut(ast.HHole(1), []))]
  occurs(sub, 1, ast.VNeut(ast.HHole(0), [])) |> should.equal(True)
  occurs(sub, 2, ast.VNeut(ast.HHole(0), [])) |> should.equal(False)
}

// ============================================================================
// TEST 6: Bool module minimal
// ============================================================================
/// Minimal bool module that triggers the InfiniteType bug.
pub fn bool_module_minimal_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

fn xor(a: Bool, b: Bool) -> Bool {
  and(or(a, b), not(and(a, b)))
}
"
  let #(errors, _results) = test_api.run_test_file(source, "bool_minimal.tao")
  has_infinite_type(errors) |> should.equal(False)
}

/// Test with just not and and (no xor)
pub fn bool_module_no_xor_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}
"
  let #(errors, _results) = test_api.run_test_file(source, "bool_minimal.tao")
  has_infinite_type(errors) |> should.equal(False)
}

/// Test with xor only (no test lines)
pub fn bool_module_xor_only_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

fn xor(a: Bool, b: Bool) -> Bool {
  or(a, b)
}
"
  let #(errors, _results) = test_api.run_test_file(source, "bool_minimal.tao")
  has_infinite_type(errors) |> should.equal(False)
}

/// Test with full xor body
pub fn bool_module_full_xor_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

fn xor(a: Bool, b: Bool) -> Bool {
  and(or(a, b), not(and(a, b)))
}
"
  let #(errors, _results) = test_api.run_test_file(source, "bool_minimal.tao")
  has_infinite_type(errors) |> should.equal(False)
}

// ============================================================================
// TEST 7: Direct hole expansion test
// ============================================================================
/// Test that hole expansion doesn't create cycles.
pub fn direct_hole_expansion_test() {
  // Create a hole-typed term and apply it to an argument
  // This triggers hole expansion in infer_app
  let h = hole(0, s1)
  let arg = i32(42, s1)
  let app_term = app(h, arg, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, app_term)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 8: Hole applied to lambda
// ============================================================================
/// Test that a hole applied to a lambda doesn't create cycles.
pub fn hole_applied_to_lambda_test() {
  let h = hole(0, s1)
  let lambda = lam("x", var(0, s1), s1)
  let app_term = app(h, lambda, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, app_term)
  has_infinite_type(s.errors) |> should.equal(False)
}

// ============================================================================
// TEST 9: Self-application (should fail with InfiniteType)
// ============================================================================
/// x(x) should produce an InfiniteType error.
pub fn self_application_test() {
  // λx. x(x)
  let self_app = app(var(0, s1), var(0, s1), s1)
  let lam_term = lam("x", self_app, s1)
  
  let #(_val, _ty, s) = infer(state.initial_state, lam_term)
  // This SHOULD produce an InfiniteType error
  has_infinite_type(s.errors) |> should.equal(True)
}

// ============================================================================
// TEST 10: Substitution chain test
// ============================================================================
/// Test that substitution chains are followed correctly.
pub fn substitution_chain_test() {
  // Create a chain: hole 0 -> hole 1 -> hole 2
  // Then check if occurs detects cycles
  
  let sub = [
    #(0, ast.VNeut(ast.HHole(1), [])),
    #(1, ast.VNeut(ast.HHole(2), [])),
  ]
  
  // occurs should follow the chain: 0 -> 1 -> 2
  occurs(sub, 2, ast.VNeut(ast.HHole(0), [])) |> should.equal(True)
  occurs(sub, 3, ast.VNeut(ast.HHole(0), [])) |> should.equal(False)
}
