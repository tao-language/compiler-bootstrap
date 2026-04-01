// ============================================================================
// IMPLICIT CONTEXT TESTS
// ============================================================================
/// Tests for implicit parameter context handling.
///
/// These tests verify that implicit parameters are correctly added to the
/// context before body inference, ensuring proper De Bruijn index handling.
import core/ast as ast
import core/state as state
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

const span = Span("test", 0, 0, 0, 0)
const s = state.initial_state

/// Test that create_implicit_bindings creates correct number of holes
pub fn create_implicit_bindings_count_test() {
  let initial_holes = s.hole
  let #(bindings, new_s) = c.create_implicit_bindings(["_0", "_1"], s)
  
  list.length(bindings) |> should.equal(2)
  new_s.hole |> should.equal(initial_holes + 2)
}

/// Test that bindings are in correct order
pub fn create_implicit_bindings_order_test() {
  let #(bindings, _) = c.create_implicit_bindings(["_a", "_b", "_c"], s)
  
  // Bindings should be in original order
  let names = list.map(bindings, fn(b) { b.0 })
  names |> should.equal(["_a", "_b", "_c"])
}

/// Test that each binding has a unique hole
pub fn create_implicit_bindings_unique_holes_test() {
  let #(bindings, _) = c.create_implicit_bindings(["_0", "_1", "_2"], s)
  
  // Extract hole IDs from bindings
  let hole_ids = list.map(bindings, fn(b) {
    case b.1.0 {
      ast.VNeut(ast.HHole(id), []) -> id
      _ -> -1
    }
  })
  
  // All hole IDs should be unique
  let unique_count = list.length(list.unique(hole_ids))
  unique_count |> should.equal(3)
}

/// Test that bindings contain HHole values
pub fn create_implicit_bindings_hole_values_test() {
  let #(bindings, _) = c.create_implicit_bindings(["_0", "_1"], s)
  
  // Each binding should have HHole value
  let all_holes = list.all(bindings, fn(b) {
    case b.1.0 {
      ast.VNeut(ast.HHole(_), []) -> True
      _ -> False
    }
  })
  
  all_holes |> should.be_true()
}

/// Test empty implicit list
pub fn create_implicit_bindings_empty_test() {
  let initial_holes = s.hole
  let #(bindings, new_s) = c.create_implicit_bindings([], s)
  
  list.length(bindings) |> should.equal(0)
  new_s.hole |> should.equal(initial_holes)
}
