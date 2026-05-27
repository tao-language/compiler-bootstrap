import core/ast
import core/state.{type Subst}
import gleam/list

/// Take this potentially suspended or indirect value,
/// look up its current state in the environment,
/// and recursively strip away wrappers until you hit the actual,
/// underlying concrete head.
pub fn unwrap(subst: Subst, value: ast.Value) -> ast.Value {
  case value {
    ast.VNeut(ast.NHole(id)) ->
      case list.key_find(subst, id) {
        Ok(solution) -> unwrap(subst, solution)
        Error(Nil) -> value
      }
    _ -> value
  }
}
