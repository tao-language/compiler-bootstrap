// Core quote - Value → Term conversion
// Quotes a value back to a term (syntax).
// Does NOT call eval - quote transforms a Value back to a Term by re-wrapping
// evaluated lambdas.

import core/ast
import core/state

/// Quote a value to a term
pub fn quote(val: ast.Value, state: state.State) -> ast.Term {
  case val {
    ast.Closure(name, body, _) -> {
      // Re-wrap the lambda with the captured environment
      ast.Lam(name, ast.TVar(0), body)
    }
    ast.IntVal(n) -> ast.IntLit(n)
    ast.FloatVal(n) -> ast.FloatLit(n)
    ast.StringVal(s) -> ast.StringLit(s)
  }
}
