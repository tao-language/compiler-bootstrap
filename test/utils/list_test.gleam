/// Tests for the utils module.
import gleam/option.{None, Some}
import utils/list_utils.{at}

pub fn list_at_index_0_test() {
  assert at([1, 2, 3], 0) == Some(1)
}

pub fn list_at_index_1_test() {
  assert at([1, 2, 3], 1) == Some(2)
}

pub fn list_at_last_index_test() {
  assert at([1, 2, 3], 2) == Some(3)
}

pub fn list_at_out_of_bounds_test() {
  assert at([1, 2, 3], 3) == None
}

pub fn list_at_negative_index_test() {
  // Negative indices are out of range: they must give None, never
  // silently bind to the head (that masking turned the factorial
  // misquoting into a silent miscompilation of `f(n-1)` into `n(n-1)`).
  assert at([1, 2, 3], -1) == None
}

pub fn list_at_arbitrary_negative_index_is_out_of_bounds_test() {
  assert at([1, 2, 3], -4) == None
  assert at([1, 2, 3], -100) == None
  assert at([], -1) == None
}

pub fn list_at_empty_list_test() {
  assert at([], 0) == None
}

pub fn list_at_single_element_test() {
  assert at([42], 0) == Some(42)
}

pub fn list_at_single_element_out_of_bounds_test() {
  assert at([42], 1) == None
}
