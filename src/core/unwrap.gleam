import core/state.{type Subst}
import core/value.{type Value} as v
import gleam/list

/// Take this potentially suspended or indirect value,
/// look up its current state in the environment,
/// and recursively strip away wrappers until you hit the actual,
/// underlying concrete head.
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
