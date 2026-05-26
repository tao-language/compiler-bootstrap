import core/ast
import core/state.{type FFI, type Subst}
import gleam/list

/// Take this potentially suspended or indirect value,
/// look up its current state in the environment,
/// and recursively strip away wrappers until you hit the actual,
/// underlying concrete head.
pub fn unwrap(ffi: FFI, subst: Subst, value: ast.Value) -> ast.Value {
  case value {
    ast.VNeut(ast.HHole(id), spine) ->
      case list.key_find(subst, id) {
        Ok(solution) -> {
          let solution = unwrap(ffi, subst, solution)
          apply_spine(ffi, solution, spine)
        }
        Error(Nil) -> value
      }
    _ -> value
  }
}

fn apply_spine(ffi: FFI, value: ast.Value, spine: List(ast.Elim)) -> ast.Value {
  case spine {
    [] -> value
    [elim, ..spine] -> {
      let value = apply_elim(ffi, value, elim)
      apply_spine(ffi, value, spine)
    }
  }
}

fn apply_elim(ffi: FFI, value: ast.Value, elim: ast.Elim) -> ast.Value {
  echo elim
  todo
}
