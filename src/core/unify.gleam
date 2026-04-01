// ============================================================================
// CORE UNIFY - Higher-Order Unification (STUB)
// ============================================================================
import gleam/list
import gleam/result
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state

pub fn unify(
  s: state.State,
  lvl: Int,
  v1: ast.Value,
  v2: ast.Value,
  span1: Span,
  span2: Span,
) -> #(ast.Subst, state.State) {
  #(s.subst, s)
}
