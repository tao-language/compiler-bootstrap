// ============================================================================
// CORE INFER - Type Inference (STUB)
// ============================================================================
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/eval as eval
import core/quote as quote
import core/subst as subst
import core/unify as unify

pub fn infer(s: state.State, term: ast.Term) -> #(ast.Value, ast.Type, state.State) {
  #(ast.VErr, ast.VErr, s)
}

pub fn infer_match(
  s: state.State,
  arg: ast.Term,
  motive: ast.Term,
  cases: List(ast.Case),
  span: Span,
) -> #(ast.Value, ast.Type, state.State) {
  #(ast.VErr, ast.VErr, s)
}
