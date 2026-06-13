import core/context.{type Context}
import core/infer.{infer}
import core/term.{type Term}
import core/value.{type Value}
import tao/ast.{type Expr}
import tao/desugar.{desugar_expr}

pub fn check_expr(ctx: Context, expr: Expr) -> #(Term, Value, Context) {
  infer(ctx, desugar_expr(expr))
}
