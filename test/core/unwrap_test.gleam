/// Tests for the `unwrap` module — hole resolution through substitutions.
///
/// These tests verify that `unwrap` correctly follows the substitution chain
/// to find the concrete underlying value.
import core/unwrap.{unwrap}
import core/value as v

pub fn unwrap_no_solution_test() {
  let solution = unwrap([], [], v.hole([], 10))
  assert solution == v.hole([], 10)
}

pub fn unwrap_direct_solution_test() {
  let subst = [#(10, v.int_t)]
  let solution = unwrap([], subst, v.hole([], 10))
  assert solution == v.int_t
}

pub fn unwrap_indirect_solution_test() {
  let subst = [#(10, v.hole([], 20)), #(20, v.int_t)]
  let solution = unwrap([], subst, v.hole([], 10))
  assert solution == v.int_t
}
