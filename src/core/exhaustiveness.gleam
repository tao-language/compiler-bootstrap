// ============================================================================
// CORE EXHAUSTIVENESS - Pattern Match Coverage Checking (STUB)
// ============================================================================
import gleam/list
import syntax/grammar.{type Span}
import core/ast as ast
import core/state as state

pub type PMatrix =
  List(List(ast.Pattern))

pub fn check_exhaustiveness(
  patterns: List(List(ast.Pattern)),
  types: List(ast.Value),
) -> List(state.Error) {
  []
}

pub fn get_default_cases(
  patterns: List(List(ast.Pattern)),
  types: List(ast.Value),
) -> List(ast.Pattern) {
  [ast.PAny]
}
