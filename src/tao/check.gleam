import core/context.{type Context}
import core/infer.{infer}
import core/term.{type Term}
import core/value.{type Value}
import tao/ast.{type Expr}
import tao/desugar

pub fn check_expr(ctx: Context, expr: Expr) -> #(Term, Value, Context) {
  infer(ctx, desugar.expr(expr))
}
