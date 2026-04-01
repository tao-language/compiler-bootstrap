// ============================================================================
// CORE GENERALIZE - Lambda Generalization (STUB)
// ============================================================================
import gleam/list
import gleam/option.{type Option, Some, None}
import syntax/grammar.{Span, type Span}
import core/ast as ast
import core/state as state

pub fn generalize_holes(
  implicit: List(String),
  domain: ast.Term,
  codomain: ast.Term,
  s: state.State,
) -> #(ast.Term, ast.Term, state.State) {
  #(domain, codomain, s)
}

pub fn create_implicit_bindings(
  implicit: List(String),
  s: state.State,
) -> #(List(#(String, ast.Term)), state.State) {
  list.fold(implicit, #([], s), fn(acc, name) {
    let #(bindings, s) = acc
    let #(id, s) = state.new_hole(s)
    let hole = ast.Hole(id, Span("", 0, 0, 0, 0))
    #([#(name, hole), ..bindings], s)
  })
}

pub fn free_holes_in_value(value: ast.Value) -> List(Int) {
  []
}
