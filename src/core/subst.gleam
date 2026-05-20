import core/ast
import core/state.{type FFI, type Subst}
import core/utils
import gleam/option.{None, Some}

pub fn force_value(ffi: FFI, sub: Subst, value: ast.Value) -> ast.Value {
  case value {
    ast.VNeut(ast.HHole(id), spine) ->
      case utils.list_lookup(sub, id) {
        Some(solution) -> {
          let solution = force_value(ffi, sub, solution)
          apply_spine(ffi, sub, solution, spine)
        }
        None -> value
      }
    _ -> value
  }
}

pub fn apply_spine(
  ffi: FFI,
  sub: Subst,
  value: ast.Value,
  spine: List(ast.Elim),
) -> ast.Value {
  case spine {
    [] -> value
    [elim, ..spine] -> {
      let value = apply_elim(ffi, sub, value, elim)
      apply_spine(ffi, sub, value, spine)
    }
  }
}

pub fn apply_elim(
  ffi: FFI,
  sub: Subst,
  value: ast.Value,
  elim: ast.Elim,
) -> ast.Value {
  echo elim
  todo
}
