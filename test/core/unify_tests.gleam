// ============================================================================
// UNIFY TESTS
// ============================================================================
/// Tests for the unify function.
///
/// These tests verify that unify correctly handles holes, literals, and
/// constructor values.
import gleam/list
import core/ast as ast
import core/state as state
import core/unify as unify
import core/subst as subst
import syntax/grammar.{Span}
import gleeunit

pub fn main() {
  test_unify_hole_with_value()
  test_unify_value_with_hole()
  test_unify_two_holes()
  test_unify_lit_with_hole()
  test_unify_hole_with_lit()
  test_unify_ctr_value_with_lit_t()
  test_unify_lit_t_with_ctr_value()
}

fn test_unify_hole_with_value() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let hole = ast.VNeut(ast.HHole(0), [])
  let value = ast.VLitT(ast.ILitT)
  
  let #(_subst, s) = unify.unify(s, 0, hole, value, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // The hole should be solved to ILitT
  let result = subst.force(s.ffi, s.subst, hole)
  case result == value {
    True -> {
      // OK - test passes
    }
    False -> panic("Hole should unify with value")
  }
}

fn test_unify_value_with_hole() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let value = ast.VLitT(ast.ILitT)
  let hole = ast.VNeut(ast.HHole(0), [])
  
  let #(_subst, s) = unify.unify(s, 0, value, hole, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // The hole should be solved to ILitT
  let result = subst.force(s.ffi, s.subst, hole)
  case result == value {
    True -> {
      // OK - test passes
    }
    False -> panic("Hole should unify with value")
  }
}

fn test_unify_two_holes() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let hole1 = ast.VNeut(ast.HHole(0), [])
  let hole2 = ast.VNeut(ast.HHole(1), [])
  
  let #(_subst, s) = unify.unify(s, 0, hole1, hole2, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // Both holes should be the same
  let result1 = subst.force(s.ffi, s.subst, hole1)
  let result2 = subst.force(s.ffi, s.subst, hole2)
  case result1 == result2 {
    True -> {
      // OK - test passes
    }
    False -> panic("Two holes should unify to the same value")
  }
}

fn test_unify_lit_with_hole() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let value = ast.VLit(ast.IntLit(42))
  let hole = ast.VNeut(ast.HHole(0), [])
  
  let #(_subst, s) = unify.unify(s, 0, value, hole, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // The hole should be solved to ILitT
  let result = subst.force(s.ffi, s.subst, hole)
  case result == ast.VLitT(ast.ILitT) {
    True -> {
      // OK - test passes
    }
    False -> panic("Hole should be solved to ILitT")
  }
}

fn test_unify_hole_with_lit() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let hole = ast.VNeut(ast.HHole(0), [])
  let value = ast.VLit(ast.IntLit(42))
  
  let #(_subst, s) = unify.unify(s, 0, hole, value, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // The hole should be solved to ILitT
  let result = subst.force(s.ffi, s.subst, hole)
  case result == ast.VLitT(ast.ILitT) {
    True -> {
      // OK - test passes
    }
    False -> panic("Hole should be solved to ILitT")
  }
}

fn test_unify_ctr_value_with_lit_t() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let ctr_val = ast.VCtrValue(ast.VCtr("True", ast.VUnit))
  let lit_t = ast.VLitT(ast.ILitT)
  
  let #(_subst, s) = unify.unify(s, 0, ctr_val, lit_t, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // Should have an error
  let has_err = list.length(s.errors) > 0
  case has_err {
    True -> {
      // OK - test passes
    }
    False -> panic("Unify should produce error for incompatible types")
  }
}

fn test_unify_lit_t_with_ctr_value() {
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  let lit_t = ast.VLitT(ast.ILitT)
  let ctr_val = ast.VCtrValue(ast.VCtr("True", ast.VUnit))
  
  let #(_subst, s) = unify.unify(s, 0, lit_t, ctr_val, Span("", 0, 0, 0, 0), Span("", 0, 0, 0, 0))
  
  // Should have an error
  let has_err = list.length(s.errors) > 0
  case has_err {
    True -> {
      // OK - test passes
    }
    False -> panic("Unify should produce error for incompatible types")
  }
}
