// ============================================================================
// CORE LIST UTILITIES
// Shared list helper functions extracted from state.gleam, eval.gleam, infer.gleam
// to avoid duplication across the core module.
// ============================================================================

/// Get an element by index from a list. Returns None if out of bounds.
/// Equivalent to list.indexed/1 |> list.find(_, fn(#(i, _)) { i == index }) |> result.map(_, fn(x) { x.1 })
/// but faster for single access since it's O(n).
pub fn list_get(list: List(a), index: Int) -> Result(a, Nil) {
  list_get_loop(list, index, 0)
}

fn list_get_loop(list: List(a), index: Int, current: Int) -> Result(a, Nil) {
  case list {
    [] -> Error(Nil)
    [x, ..xs] -> {
      case current == index {
        True -> Ok(x)
        False -> list_get_loop(xs, index, current + 1)
      }
    }
  }
}

/// Find the index of an element matching a predicate.
/// Returns Ok(index) if found, Error(Nil) if not.
pub fn find_index(list: List(a), predicate: fn(a) -> Bool) -> Result(Int, Nil) {
  find_index_loop(list, predicate, 0)
}

fn find_index_loop(list: List(a), predicate: fn(a) -> Bool, index: Int) -> Result(Int, Nil) {
  case list {
    [] -> Error(Nil)
    [x, ..xs] -> {
      case predicate(x) {
        True -> Ok(index)
        False -> find_index_loop(xs, predicate, index + 1)
      }
    }
  }
}
