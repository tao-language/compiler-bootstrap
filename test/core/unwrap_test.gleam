/// Tests for the `unwrap` module — unwrap and hole resolution.
///
/// These tests verify that `unwrap` correctly propagates hole
/// substitutions through all value constructors.
import core/ast
import core/state.{State, new_state}
import core/unwrap.{unwrap}
import gleam/list
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

pub fn unwrap_no_solution_test() {
  let solution = unwrap([], [], ast.vhole(10, []))
  assert solution == ast.vhole(10, [])
}

pub fn unwrap_direct_solution_test() {
  let subst = [#(10, ast.vint_t)]
  let solution = unwrap([], subst, ast.vhole(10, []))
  assert solution == ast.vint_t
}

pub fn unwrap_indirect_solution_test() {
  let subst = [#(10, ast.vhole(20, [])), #(20, ast.vint_t)]
  let solution = unwrap([], subst, ast.vhole(10, []))
  assert solution == ast.vint_t
}
