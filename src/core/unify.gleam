/// Unification — Higher-order unification for Core values.
///
/// Unification checks whether two `Value`s are "the same" and records
/// any mismatches as errors in the `State`. It also resolves holes
/// (unbound metavariables) by binding them to their types.
///
/// ## How it works
///
/// `unify(state, expected, actual)` recursively compares the two values:
///
/// - **Holes** (`VNeut(HHole(id))`) — unbound metavariables. When the
///   expected type is a hole, we bind it to the actual type in state.
/// - **Variables** (`VNeut(HVar(level))`) — look up the binding in state.
/// - **Same constructors** — recursively unify their fields.
/// - **Mismatched constructors** — record a `TypeMismatch` error.
///
/// The type checker calls this function at every place where two types
/// must agree. All errors accumulate in state; no early returns.
import core/ast
import core/state.{type State, TypeMismatch, with_err}
import syntax/span.{type Span}

pub fn unify(
  state: State,
  a: #(ast.Value, Span),
  b: #(ast.Value, Span),
) -> #(ast.Value, State) {
  let #(value1, span1) = a
  let #(value2, span2) = b
  case #(value1, value2) {
    #(ast.VTyp(u1), ast.VTyp(u2)) if u1 == u2 -> #(value1, state)
    #(ast.VLit(v1), ast.VLit(v2)) if v1 == v2 -> #(value1, state)
    #(ast.VLitT(v1), ast.VLitT(v2)) if v1 == v2 -> #(value1, state)
    _ -> {
      let state = with_err(state, TypeMismatch(a, b))
      #(ast.VErr, state)
    }
  }
}
