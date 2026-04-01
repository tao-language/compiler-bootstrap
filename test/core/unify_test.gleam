// ============================================================================
// UNIFICATION TESTS
// ============================================================================
/// Tests for the unification algorithm.
///
/// Unification checks type equality and solves constraints.
/// It's the core algorithm for type checking with holes and inference.
import core/ast as ast
import core/state as state
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import core/unify.{unify}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS (shared with other test modules)
// ============================================================================

const s = state.initial_state

const s1 = Span("unify_test", 1, 1, 1, 1)

const s2 = Span("unify_test", 2, 2, 2, 2)

fn v32(v) {
  ast.VLit(ast.I32(v))
}

fn v64(v) {
  ast.VLit(ast.I64(v))
}

const v32t = ast.VLitT(ast.I32T)

const v64t = ast.VLitT(ast.I64T)

fn vhole(i) {
  ast.VNeut(ast.HHole(i), [])
}

// ============================================================================
// BASIC TYPE UNIFICATION
// ============================================================================

pub fn unify_typ_equal_level_zero_test() {
  // Types at same level unify successfully
  unify(s, ast.VTyp(0), ast.VTyp(0), s1, s2) |> should.equal(Ok(s))
}

pub fn unify_typ_equal_level_one_test() {
  // Types at level 1 unify successfully
  unify(s, ast.VTyp(1), ast.VTyp(1), s1, s2) |> should.equal(Ok(s))
}

pub fn unify_typ_mismatch_test() {
  // Types at different levels fail to unify
  unify(s, ast.VTyp(0), ast.VTyp(1), s1, s2)
  |> should.equal(Error(state.TypeMismatch(ast.VTyp(0), ast.VTyp(1), s1, s2)))
}

// ============================================================================
// LITERAL VALUE UNIFICATION
// ============================================================================

pub fn unify_i32_equal_test() {
  // Same I32 values unify
  unify(s, v32(1), v32(1), s1, s2) |> should.equal(Ok(s))
}

pub fn unify_i64_equal_test() {
  // Same I64 values unify
  unify(s, v64(2), v64(2), s1, s2) |> should.equal(Ok(s))
}

pub fn unify_lit_mismatch_test() {
  // Different I32 values fail to unify
  unify(s, v32(1), v32(2), s1, s2)
  |> should.equal(Error(state.TypeMismatch(v32(1), v32(2), s1, s2)))
}

// ============================================================================
// LITERAL TYPE UNIFICATION
// ============================================================================

pub fn unify_i32t_equal_test() {
  // Same literal types unify
  unify(s, v32t, v32t, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_i64t_equal_test() {
  unify(s, v64t, v64t, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_litt_mismatch_test() {
  // Different literal types fail to unify
  unify(s, v32t, v64t, s1, s2)
  |> should.equal(Error(state.TypeMismatch(v32t, v64t, s1, s2)))
}

// ============================================================================
// HOLE UNIFICATION
// ============================================================================

pub fn unify_hole_solve_test() {
  // Solving an unsolved hole
  unify(s, vhole(0), v32t, s1, s2)
  |> should.equal(Ok(state.State(..s, sub: [#(0, v32t)])))

  // Symmetric case
  unify(s, v32t, vhole(0), s1, s2)
  |> should.equal(Ok(state.State(..s, sub: [#(0, v32t)])))
}

pub fn unify_hole_already_solved_test() {
  // Hole already solved to v32t, unify with v32t succeeds
  let s = state.State(..s, sub: [#(0, v32t)])
  unify(s, vhole(0), v32t, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_hole_occurs_check_test() {
  // Occurs check: hole cannot be solved to a type containing itself
  // Note: This tests the occurs check through a neutral term spine
  let val = ast.VNeut(ast.HHole(0), [ast.EApp(v32t)])
  unify(s, vhole(0), val, s1, s2)
  |> should.equal(Error(state.InfiniteType(0, val, s1, s2)))
}

pub fn unify_hole_with_itself_test() {
  // A hole unifying with itself should succeed (no infinite type error)
  // This is critical for lambda type inference: λx. x should work
  unify(s, vhole(0), vhole(0), s1, s2) |> should.equal(Ok(s))
}

pub fn unify_hole_with_neutral_hole_test() {
  // Hole unifying with neutral term containing same hole should fail
  let val = ast.VNeut(ast.HHole(0), [ast.EApp(v32t)])
  unify(s, vhole(0), val, s1, s2)
  |> should.equal(Error(state.InfiniteType(0, val, s1, s2)))
}

pub fn unify_hole_with_different_hole_test() {
  // Two different holes should unify (first solves to second)
  let result = unify(s, vhole(0), vhole(1), s1, s2)
  case result {
    Ok(s) -> {
      // Hole 0 should be solved to hole 1
      list.key_find(s.sub, 0) |> should.equal(Ok(vhole(1)))
    }
    Error(_) -> should.fail()
  }
}

// ============================================================================
// NEUTRAL TERM UNIFICATION
// ============================================================================

pub fn unify_neut_equal_test() {
  // Same head and spine
  let v1 = ast.VNeut(ast.HVar(0), [ast.EDot("x")])
  let v2 = ast.VNeut(ast.HVar(0), [ast.EDot("x")])
  unify(s, v1, v2, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_neut_head_mismatch_test() {
  // Different heads should fail
  let v1 = ast.VNeut(ast.HVar(0), [])
  let v2 = ast.VNeut(ast.HVar(1), [])
  unify(s, v1, v2, s1, s2)
  |> should.equal(Error(state.TypeMismatch(v1, v2, s1, s2)))
}

// ============================================================================
// RECORD UNIFICATION
// ============================================================================

pub fn unify_rcd_equal_test() {
  let v1 = ast.VRcd([#("a", v32t)])
  let v2 = ast.VRcd([#("a", v32t)])
  unify(s, v1, v2, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_rcd_field_order_test() {
  // Field order shouldn't matter
  let v1 = ast.VRcd([#("a", v32t), #("b", v64t)])
  let v2 = ast.VRcd([#("b", v64t), #("a", v32t)])
  unify(s, v1, v2, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_rcd_missing_field_test() {
  let v1 = ast.VRcd([#("a", v32t)])
  let v2 = ast.VRcd([])
  unify(s, v1, v2, s1, s2)
  |> should.equal(Error(state.RcdMissingFields(["a"], s2)))
}

// ============================================================================
// CONSTRUCTOR UNIFICATION
// ============================================================================

pub fn unify_ctr_equal_test() {
  let v1 = ast.VCtrValue(ast.VCtr("A", v32t))
  let v2 = ast.VCtrValue(ast.VCtr("A", v32t))
  unify(s, v1, v2, s1, s2) |> should.equal(Ok(s))
}

pub fn unify_ctr_tag_mismatch_test() {
  let v1 = ast.VCtrValue(ast.VCtr("A", v32t))
  let v2 = ast.VCtrValue(ast.VCtr("B", v32t))
  unify(s, v1, v2, s1, s2)
  |> should.equal(Error(state.TypeMismatch(v1, v2, s1, s2)))
}

// ============================================================================
// FUNCTION TYPE UNIFICATION
// ============================================================================

pub fn unify_lam_equal_test() {
  let v1 = ast.VLam([], "x", [], ast.Var(0, s1))
  let v2 = ast.VLam([], "y", [], ast.Var(0, s1))
  unify(s, v1, v2, s1, s2)
  |> should.equal(Ok(state.State(..s, var: 1)))
}

pub fn unify_pi_equal_test() {
  let v1 = ast.VPi([], "x", [], v32t, ast.Var(0, s1))
  let v2 = ast.VPi([], "y", [], v32t, ast.Var(0, s1))
  unify(s, v1, v2, s1, s2)
  |> should.equal(Ok(state.State(..s, var: 1)))
}

pub fn unify_pi_domain_mismatch_test() {
  let v1 = ast.VPi([], "x", [], v32t, ast.Var(0, s1))
  let v2 = ast.VPi([], "x", [], v64t, ast.Var(0, s1))
  unify(s, v1, v2, s1, s2)
  |> should.equal(Error(state.TypeMismatch(v32t, v64t, s1, s2)))
}

pub fn unify_pi_with_holes_test() {
  // Test basic hole unification first
  let basic_result = unify(s, vhole(0), v32t, s1, s2)
  case basic_result {
    Ok(basic_s) -> {
      // Check the state - hole 0 should be solved
      list.length(basic_s.sub) |> should.equal(1)
    }
    Error(_) -> should.fail()
  }

  // Now test full Pi unification
  let v1 = ast.VPi([], "x", [], vhole(0), ast.Var(0, s1))
  let v2 = ast.VPi([], "x", [], v32t, ast.Var(0, s1))
  let result = unify(s, v1, v2, s1, s2)
  case result {
    Ok(pi_s) -> {
      // Check that hole 0 was solved in the Pi unification
      list.key_find(pi_s.sub, 0) |> should.equal(Ok(v32t))
    }
    Error(_) -> should.fail()
  }
}

pub fn unify_lam_with_holes_test() {
  // Lambda types with holes should unify
  let env = []
  let v1 = ast.VLam([], "x", env, ast.Var(0, s1))
  let v2 = ast.VLam([], "y", env, ast.Var(0, s1))
  unify(s, v1, v2, s1, s2)
  |> should.equal(Ok(state.State(..s, var: 1)))
}

// ============================================================================
// ERROR TYPE UNIFICATION
// ============================================================================

pub fn unify_verr_test() {
  // VErr always unifies successfully (error recovery)
  unify(s, ast.VErr, v32t, s1, s2) |> should.equal(Ok(s))
  unify(s, v32t, ast.VErr, s1, s2) |> should.equal(Ok(s))
  unify(s, ast.VErr, ast.VErr, s1, s2) |> should.equal(Ok(s))
}
