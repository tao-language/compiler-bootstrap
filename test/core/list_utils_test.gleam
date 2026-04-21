// ============================================================================
// CORE LIST UTILITIES TEST
// ============================================================================
import core/list_utils
import gleeunit
import gleeunit/should

// ============================================================================
// LIST_GET TESTS
// ============================================================================

pub fn test_list_get_first() {
  list_utils.list_get([1, 2, 3], 0)
  |> should.equal(Ok(1))
}

pub fn test_list_get_middle() {
  list_utils.list_get([1, 2, 3, 4], 2)
  |> should.equal(Ok(3))
}

pub fn test_list_get_out_of_bounds() {
  list_utils.list_get([1, 2, 3], 5)
  |> should.equal(Error(Nil))
}

pub fn test_list_get_empty() {
  list_utils.list_get([], 0)
  |> should.equal(Error(Nil))
}

// ============================================================================
// FIND_INDEX TESTS
// ============================================================================

pub fn test_find_index_existing() {
  list_utils.find_index([10, 20, 30, 40], fn(n) { n == 30 })
  |> should.equal(Ok(2))
}

pub fn test_find_index_not_found() {
  list_utils.find_index([1, 2, 3], fn(n) { n == 10 })
  |> should.equal(Error(Nil))
}

pub fn test_find_index_empty() {
  list_utils.find_index([], fn(_n) { True })
  |> should.equal(Error(Nil))
}
