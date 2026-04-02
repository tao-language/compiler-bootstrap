// ============================================================================
// CORE CHECK - Type Checking
// ============================================================================
/// Bidirectional type checking: verify terms have expected types.
///
/// This module re-exports check functions from core/infer to maintain
/// the original module structure while avoiding import cycles.
import gleam/list
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state
import core/infer

pub fn check(
  s: state.State,
  term: ast.Term,
  expected_ty: ast.Type,
  ty_span: Span,
) -> #(ast.Value, state.State) {
  infer.check(s, term, expected_ty, ty_span)
}

pub fn check_type(
  s: state.State,
  t1: ast.Value,
  t2: ast.Value,
  t1_span: Span,
  t2_span: Span,
) -> #(state.State, List(#(String, ast.Value))) {
  infer.check_type(s, t1, t2, t1_span, t2_span)
}

pub fn check_ctr_def(
  s: state.State,
  ctr: ast.CtrDef,
) -> #(List(Int), ast.Value, ast.Value, state.State) {
  infer.check_ctr_def(s, ctr)
}
