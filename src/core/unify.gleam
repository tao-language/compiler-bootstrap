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
import core/state.{type State, State, TypeMismatch, with_err}
import core/utils
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

pub fn unify(
  state: State,
  a: #(ast.Value, Span),
  b: #(ast.Value, Span),
) -> State {
  let #(value1, span1) = a
  let #(value2, span2) = b
  case value1, value2 {
    ast.VTyp(u1), ast.VTyp(u2) if u1 == u2 -> state
    ast.VLit(v1), ast.VLit(v2) if v1 == v2 -> state
    ast.VLitT(v1), ast.VLitT(v2) if v1 == v2 -> state
    ast.VNeut(h1, spine1), ast.VNeut(h2, spine2) if h1 == h2 ->
      unify_spines(state, spine1, spine2)
    _, ast.VNeut(ast.HHole(id), _) -> solve_hole(state, #(id, span2), a)
    ast.VNeut(ast.HHole(id), _), _ -> solve_hole(state, #(id, span1), b)
    _, _ -> with_err(state, TypeMismatch(a, b))
  }
}

fn solve_hole(state: State, a: #(Int, Span), b: #(ast.Value, Span)) -> State {
  let #(hole_id, span1) = a
  let #(value, span2) = b
  case utils.list_lookup(state.subst, hole_id) {
    Some(solution) -> unify(state, #(solution, span1), #(value, span2))
    None -> State(..state, subst: [#(hole_id, value), ..state.subst])
  }
}

fn unify_spines(
  state: State,
  spine1: List(ast.Elim),
  spine2: List(ast.Elim),
) -> State {
  case spine1, spine2 {
    [], [] -> state
    [a, ..spine1], [b, ..spine2] -> {
      let state = unify_elim(state, a, b)
      unify_spines(state, spine1, spine2)
    }
    _, _ -> with_err(state, state.SpineArityMismatch(spine1, spine2))
  }
}

fn unify_elim(state: State, elim1: ast.Elim, elim2: ast.Elim) -> State {
  case elim1, elim2 {
    ast.EApp(arg1, span1), ast.EApp(arg2, span2) ->
      unify(state, #(arg1, span1), #(arg2, span2))
    ast.EMatch(env1, cases1, span1), ast.EMatch(env2, cases2, span2) -> todo
    _, _ -> with_err(state, state.SpineElimMismatch(elim1, elim2))
  }
}
