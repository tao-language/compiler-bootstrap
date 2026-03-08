// ============================================================================
// CALCULATOR FORMATTER
// ============================================================================
/// Format calculator expressions with correct precedence

import calc/ast.{type Expr, Add, Int, Mul}
import gleam/int

pub fn format(expr: Expr) -> String {
  format_expr(expr, 0)
}

fn format_expr(expr: Expr, precedence: Int) -> String {
  case expr {
    Int(n) -> int.to_string(n)
    Add(left, right) -> {
      let left_str = format_expr(left, 1)
      let right_str = format_expr(right, 1)
      left_str <> " + " <> right_str
    }
    Mul(left, right) -> {
      // Add parens if inside Add (lower precedence)
      let left_str = format_group(left, 2)
      let right_str = format_group(right, 2)
      left_str <> " * " <> right_str
    }
  }
}

fn format_group(expr: Expr, precedence: Int) -> String {
  case expr {
    Add(_, _) -> "(" <> format(expr) <> ")"
    _ -> format(expr)
  }
}
