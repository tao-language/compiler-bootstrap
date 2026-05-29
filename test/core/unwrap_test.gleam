/// Tests for the `unwrap` module — unwrap and hole resolution.
///
/// These tests verify that `unwrap` correctly propagates hole
/// substitutions through all value constructors.
import core/context.{type Subst}
import core/unwrap.{unwrap}
import core/value.{type Value} as v
import gleeunit

pub fn main() {
  gleeunit.main()
}

pub fn unwrap_no_solution_test() {
  let solution = unwrap([], v.hole(10))
  assert solution == v.hole(10)
}

pub fn unwrap_direct_solution_test() {
  let subst: Subst = [#(10, v.int_t)]
  let solution = unwrap(subst, v.hole(10))
  assert solution == v.int_t
}

pub fn unwrap_indirect_solution_test() {
  let subst: Subst = [#(10, v.hole(20)), #(20, v.int_t)]
  let solution = unwrap(subst, v.hole(10))
  assert solution == v.int_t
}
