// ============================================================================
// CALCULATOR EVALUATOR
// ============================================================================

/// Evaluate calculator expressions
import calc/ast.{type Expr, Add, Int, Mul}

pub fn eval(expr: Expr) -> Int {
  case expr {
    Int(n) -> n
    Add(left, right) -> eval(left) + eval(right)
    Mul(left, right) -> eval(left) * eval(right)
  }
}
