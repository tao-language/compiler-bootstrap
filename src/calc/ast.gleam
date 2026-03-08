// ============================================================================
// CALCULATOR AST
// ============================================================================
/// Simple calculator expression AST

pub type Expr {
  Int(Int)
  Add(Expr, Expr)
  Mul(Expr, Expr)
}
