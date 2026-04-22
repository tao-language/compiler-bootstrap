// ============================================================================
// SUBSTITUTION TESTS
// ============================================================================
/// Tests for the substitution module.
///
/// Covers:
/// - `force` - resolving holes through substitutions (edge cases beyond force_test.gleam)
/// - `ctr_solve_params` - solving constructor parameters
/// - `free_holes_in_value` - finding free holes in values
/// - `instantiate_implicit_params` - creating fresh holes for implicit params
/// - `subst_value_with_implicit_vars` / `subst_term_with_implicit_vars`
///   - substituting implicit parameter indices in values and terms

import core/ast as ast
import core/state as state
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/subst.{force, ctr_solve_params, free_holes_in_value, instantiate_implicit_params, subst_value_with_implicit_vars, subst_term_with_implicit_vars}
import gleam/option.{type Option, None}
import gleam/list

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const span = Span("subst_test", 1, 1, 1, 1)

fn vhole(id) {
  ast.VNeut(ast.HHole(id), [])
}

fn vvar(id) {
  ast.VNeut(ast.HVar(id), [])
}

fn v32(val) {
  ast.VLit(ast.I32(val))
}

fn v32t() {
  ast.VLitT(ast.I32T)
}

fn make_state() {
  state.State(..state.initial_state, errors: [], subst: [], hole_counter: 0)
}

// ============================================================================
// FORCE - Edge cases not covered by force_test.gleam
// ============================================================================

pub fn force_step_limit_test() {
  // Force should not loop infinitely - step limit prevents infinite recursion
  let sub = [#(0, vhole(0))]  // Self-referential hole
  let v = vhole(0)
  let result = force([], sub, v)
  // Should return the original value (step limit hit)
  case result {
    ast.VNeut(ast.HHole(_), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn force_with_complex_spine_test() {
  // Force should correctly handle a hole with a complex spine
  let sub = [#(0, ast.VLam([], "x", [], ast.Var(0, span)))]
  let v = ast.VNeut(ast.HHole(0), [
    ast.EApp(v32(1)),
    ast.EApp(v32(2)),
  ])
  let result = force([], sub, v)
  // After applying the spine twice to the lambda body (Var(0)),
  // we get the last argument: v32(2)
  case result {
    ast.VLit(ast.I32(2)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn force_neutral_head_preserved_test() {
  // Neutral head that isn't a hole should be preserved
  let v = ast.VNeut(ast.HVar(5), [ast.EApp(v32(1))])
  force([], [], v) |> should.equal(v)
}

// ============================================================================
// CTR SOLVE PARAMS
// ============================================================================

pub fn ctr_solve_params_all_solved_test() {
  // When all parameters are solved, returns the values
  let s = state.State(..make_state(), subst: [#(0, v32(42)), #(1, ast.VUnit)])
  let #(params, result_s) = ctr_solve_params(s, ast.CtrDef([], ast.Typ(0, span), ast.Typ(0, span)), [0, 1], "Some", span)
  params |> should.equal([ast.VUnit, v32(42)])
  result_s.errors |> should.equal([])
}

pub fn ctr_solve_params_one_unsolved_test() {
  // When a parameter is unsolved, it returns VErr and records error
  let s = state.State(..make_state(), subst: [#(0, v32(42))])
  let #(params, result_s) = ctr_solve_params(s, ast.CtrDef([], ast.Typ(0, span), ast.Typ(0, span)), [0, 2], "Some", span)
  params |> should.equal([ast.VErr, v32(42)])
  case result_s.errors {
    [state.CtrUnsolvedParam(_, _, 2, _), ..] -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn ctr_solve_params_all_unsolved_test() {
  // When all parameters are unsolved, all are VErr
  let s = make_state()
  let #(params, result_s) = ctr_solve_params(s, ast.CtrDef([], ast.Typ(0, span), ast.Typ(0, span)), [0, 1], "Some", span)
  params |> should.equal([ast.VErr, ast.VErr])
  list.length(result_s.errors) |> should.equal(2)
}

// ============================================================================
// FREE HOLE IN VALUE
// ============================================================================

pub fn free_holes_empty_value_test() {
  // No holes in a simple value
  free_holes_in_value(v32(42)) |> should.equal([])
  free_holes_in_value(ast.VUnit) |> should.equal([])
}

pub fn free_holes_single_hole_test() {
  // Single hole returns its ID
  free_holes_in_value(vhole(5)) |> should.equal([5])
}

pub fn free_holes_multiple_holes_test() {
  // Multiple distinct holes return all IDs
  let v = ast.VNeut(ast.HHole(1), [ast.EApp(vhole(2))])
  let holes = free_holes_in_value(v)
  list.length(holes) |> should.equal(2)
  list.contains(holes, 1) |> should.be_true
  list.contains(holes, 2) |> should.be_true
}

pub fn free_holes_lambda_with_hole_test() {
  // Lambda body containing a hole
  let body = ast.Lam([], #("x", ast.Var(1, span)), ast.Hole(3, span), span)
  let v = ast.VLam([], "x", [v32(1)], body)
  free_holes_in_value(v) |> should.equal([3])
}

pub fn free_holes_pi_with_hole_test() {
  // Pi type containing a hole in domain
  let in_val = vhole(7)
  // VPi takes a Term for out_term, not a Value
  let out_term = ast.Lam([], #("y", ast.Var(1, span)), ast.Var(0, span), span)
  let v = ast.VPi([], "t", [v32t()], in_val, out_term)
  free_holes_in_value(v) |> should.equal([7])
}

pub fn free_holes_record_test() {
  // Record containing a hole
  let v = ast.VRecord([#("x", vhole(4)), #("y", v32(1))])
  free_holes_in_value(v) |> should.equal([4])
}

pub fn free_holes_ctr_value_test() {
  // Constructor value containing a hole in its argument
  let v = ast.VCtrValue(ast.VCtr("Some", vhole(9)))
  free_holes_in_value(v) |> should.equal([9])
}

pub fn free_holes_call_test() {
  // Call with holes in args
  let v = ast.VCall("f", [vhole(1), vhole(2)], vhole(3))
  let holes = free_holes_in_value(v)
  list.length(holes) |> should.equal(3)
  list.contains(holes, 1) |> should.be_true
  list.contains(holes, 2) |> should.be_true
  list.contains(holes, 3) |> should.be_true
}

pub fn free_holes_fix_test() {
  // Fixpoint with holes in body
  let body = ast.Lam([], #("f", ast.Var(1, span)), ast.Hole(6, span), span)
  let v = ast.VFix("rec", [v32(1)], body)
  free_holes_in_value(v) |> should.equal([6])
}

pub fn free_holes_neutral_spine_test() {
  // Neutral with holes in spine
  let v = ast.VNeut(ast.HVar(0), [ast.EApp(vhole(5)), ast.EApp(vhole(6))])
  let holes = free_holes_in_value(v)
  list.length(holes) |> should.equal(2)
  list.contains(holes, 5) |> should.be_true
  list.contains(holes, 6) |> should.be_true
}

pub fn free_holes_no_duplicates_test() {
  // Duplicate holes should not appear multiple times
  let v = ast.VNeut(ast.HHole(5), [])
  let holes = free_holes_in_value(v)
  list.length(holes) |> should.equal(1)
}

pub fn free_holes_vctr_test() {
  // VCtr inside VCtrValue - find holes in the arg
  let v = ast.VCtrValue(ast.VCtr("Just", vhole(3)))
  free_holes_in_value(v) |> should.equal([3])
}

// ============================================================================
// INSTANTIATE IMPLICIT PARAMS
// ============================================================================

pub fn instantiate_implicit_params_empty_test() {
  // Empty implicit params list produces no bindings
  let #(bindings, s) = instantiate_implicit_params([], make_state())
  bindings |> should.equal([])
  s.hole_counter |> should.equal(0)
}

pub fn instantiate_implicit_params_one_test() {
  // One implicit param creates one fresh hole
  let #(bindings, s) = instantiate_implicit_params(["x"], make_state())
  list.length(bindings) |> should.equal(1)
  // First binding created with index 0
  case list.first(bindings) {
    Ok(#(0, _)) -> True
    _ -> False
  } |> should.be_true
  s.hole_counter |> should.equal(1)
}

pub fn instantiate_implicit_params_multiple_test() {
  // Multiple implicit params create sequential holes
  let #(bindings, s) = instantiate_implicit_params(["a", "b", "c"], make_state())
  list.length(bindings) |> should.equal(3)
  s.hole_counter |> should.equal(3)
}

// ============================================================================
// SUBST VALUE WITH IMPLICIT VARS
// ============================================================================

pub fn subst_value_implicit_var_identity_test() {
  // Non-var value is unchanged when no matching substitution
  let v = v32(42)
  subst_value_with_implicit_vars([], v) |> should.equal(v)
}

pub fn subst_value_implicit_hvar_replacement_test() {
  // HVar index maps to its replacement in the substitution
  let sub = [#(0, v32(99))]
  let v = vvar(0)
  let result = subst_value_with_implicit_vars(sub, v)
  result |> should.equal(v32(99))
}

pub fn subst_value_implicit_hvar_no_match_test() {
  // HVar with no matching substitution is unchanged
  let sub = [#(0, v32(99))]
  let v = vvar(5)  // Not in substitution
  let result = subst_value_with_implicit_vars(sub, v)
  case result {
    ast.VNeut(ast.HVar(5), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_value_implicit_lambda_body_test() {
  // Implicit params are substituted in lambda body
  let sub = [#(0, v32(99))]
  // VLam body is a Term - Var(0) represents the implicit param at index 0
  let body = ast.Lam([], #("f", ast.Var(1, span)), ast.Var(0, span), span)
  let v = ast.VLam([], "f", [v32(1)], body)
  let result = subst_value_with_implicit_vars(sub, v)
  // The Var(0) in body should be replaced by I32(99) from the substitution
  case result {
    ast.VLam(_, _, _, ast.Lam(_, _, ast.Var(0, _), _)) -> False |> should.be_true
    ast.VLam(_, _, _, ast.Lam(_, _, ast.Lit(_, _), _)) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_value_implicit_pi_preserved_test() {
  // Pi types should not substitute their binders
  let sub = [#(0, v32(99))]
  let in_val = vhole(0)  // hole at index 0
  // Create a Term (not Value) for out_term
  let out_term = ast.Lam([], #("x", ast.Var(1, span)), ast.Var(0, span), span)
  let v = ast.VPi([], "t", [], in_val, out_term)
  let result = subst_value_with_implicit_vars(sub, v)
  // Pi should be preserved with original domain (hole still at index 0)
  case result {
    ast.VPi(_, _, _, ast.VNeut(ast.HHole(0), []), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// SUBST TERM WITH IMPLICIT VARS
// ============================================================================

pub fn subst_term_implicit_var_replacement_test() {
  // Var at substituted index is replaced based on what the sub maps it to.
  // When subst maps index 0 to VNeut(HHole(5), []), Var(0) becomes Hole(5).
  let sub = [#(0, vhole(5))]
  let term = ast.Var(0, span)
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Hole(5, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_hvar_forward_test() {
  // Var maps to another HVar in subst
  let sub = [#(0, vvar(3))]
  let term = ast.Var(0, span)
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Var(3, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_var_default_test() {
  // Var not in subst (or subst contains non-HHole/HVar) keeps Var(index)
  let sub = [#(0, v32(42))]  // VLit is not HHole or HVar
  let term = ast.Var(0, span)
  let result = subst_term_with_implicit_vars(sub, term)
  // Default case: returns Var(index) since sub doesn't contain HHole or HVar
  case result {
    ast.Var(0, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_var_no_match_test() {
  // Var not in substitution is unchanged
  let sub = [#(0, v32(42))]
  let term = ast.Var(99, span)
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Var(99, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_hole_identity_test() {
  // Holes are unchanged (we only substitute vars, not holes)
  let sub = [#(0, v32(42))]
  let term = ast.Hole(5, span)
  let result = subst_term_with_implicit_vars(sub, term)
  // The hole in the term should not be affected (we only look up var indices)
  case result {
    ast.Hole(5, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_lambda_preserved_test() {
  // Lambdas are preserved - no substitution under binders
  let sub = [#(0, v32(42))]
  let param = #("x", ast.Var(1, span))
  let term = ast.Lam([], param, ast.Var(0, span), span)
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Lam(_, _, ast.Var(0, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_app_test() {
  // App nodes: both fun and arg are visited by the visitor
  // Var not in subst keeps its Var(index)
  let term = ast.App(ast.Var(0, span), [], ast.Var(1, span), span)
  let sub = [#(0, vhole(5)), #(1, vhole(6))]  // HHole substitutions
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.App(ast.Hole(5, _), _, ast.Hole(6, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_pi_test() {
  // Pi: both in and out are visited
  let term = ast.Pi([], "x", ast.Var(0, span), ast.Var(1, span), span)
  let sub = [#(0, vhole(10)), #(1, vhole(11))]  // HHole substitutions
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Pi(_, _, ast.Hole(10, _), ast.Hole(11, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn subst_term_implicit_match_test() {
  // Match: arg and motive are visited, case body is visited
  let pattern = ast.PCtr("Some", ast.PAny)
  let term = ast.Match(
    arg: ast.Var(0, span),
    motive: ast.Var(1, span),
    cases: [
      ast.Case(
        pattern: pattern,
        body: ast.Var(2, span),
        guard: None,
        span: span,
      ),
    ],
    span: span,
  )
  let sub = [#(0, vhole(20)), #(1, vhole(21)), #(2, vhole(22))]
  let result = subst_term_with_implicit_vars(sub, term)
  case result {
    ast.Match(ast.Hole(20, _), ast.Hole(21, _), cases, _) -> {
      case cases {
        [ast.Case(_, ast.Hole(22, _), None, _), ..] -> True |> should.be_true
        _ -> False |> should.be_true
      }
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn subst_empty_substitution_test() {
  // Empty substitution should return values unchanged
  let v = v32(42)
  force([], [], v) |> should.equal(v)
  subst_value_with_implicit_vars([], v) |> should.equal(v)
}

pub fn free_holes_rctd_test() {
  // VRcd (not VRecord) containing a hole
  let v = ast.VRcd([#("x", vhole(8))])
  free_holes_in_value(v) |> should.equal([8])
}
