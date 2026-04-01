// ============================================================================
// CORE CHECK - Type Checking (STUB)
// ============================================================================
import gleam/list
import gleam/option.{Some, None}
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state

pub fn check(
  s: state.State,
  term: ast.Term,
  expected: ast.Type,
  steps: Int,
) -> #(ast.Value, ast.Type, state.State) {
  #(ast.VErr, expected, s)
}

pub fn bind_pattern(
  s: state.State,
  pattern: ast.Pattern,
  value: ast.Value,
  expected: ast.Type,
) -> #(state.State, List(#(String, ast.Value))) {
  #(s, [])
}

pub fn check_ctr_def(
  s: state.State,
  ctr: ast.CtrDef,
) -> #(List(Int), ast.Value, ast.Value, state.State) {
  let ast.CtrDef(params, arg_ty, ret_ty) = ctr
  let param_indices = list.map(params, fn(_) { 0 })
  #(param_indices, ast.VErr, ast.VErr, s)
}
