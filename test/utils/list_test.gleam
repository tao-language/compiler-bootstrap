/// Tests for the utils module.
import gleam/option.{None, Some}
import utils/list_utils.{list_at}

pub fn list_at_index_0_test() {
  assert list_at([1, 2, 3], 0) == Some(1)
}

pub fn list_at_index_1_test() {
  assert list_at([1, 2, 3], 1) == Some(2)
}

pub fn list_at_last_index_test() {
  assert list_at([1, 2, 3], 2) == Some(3)
}

pub fn list_at_out_of_bounds_test() {
  assert list_at([1, 2, 3], 3) == None
}

pub fn list_at_negative_index_test() {
  // Negative index: only matches if <= 0, which catches negatives
  assert list_at([1, 2, 3], -1) == Some(1)
}

pub fn list_at_empty_list_test() {
  assert list_at([], 0) == None
}

pub fn list_at_single_element_test() {
  assert list_at([42], 0) == Some(42)
}

pub fn list_at_single_element_out_of_bounds_test() {
  assert list_at([42], 1) == None
}
