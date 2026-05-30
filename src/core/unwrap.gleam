import core/context.{type Subst}
import core/value.{type Value} as v
import gleam/list

/// Looks up a hole in the substitution table,
/// recursively stripping away solved wrappers.
pub fn unwrap(subst: Subst, value: Value) -> Value {
  case value {
    v.Neut(v.NHole(id)) ->
      case list.key_find(subst, id) {
        Ok(solution) -> unwrap(subst, solution)
        Error(Nil) -> value
      }
    _ -> value
  }
}
