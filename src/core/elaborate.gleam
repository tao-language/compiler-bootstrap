import core/ast.{type AST}
import core/context.{type Context}
import core/infer.{infer}
import core/resolve.{resolve}
import core/term.{type Term}
import core/unwrap.{unwrap}
import core/value.{type Value}

pub fn elaborate(ctx: Context, ast: AST) -> #(Term, Value) {
  let #(term, type_, ctx) = infer(ctx, ast)
  let term = resolve(ctx.subst, term)
  let type_ = unwrap(ctx.ffi, ctx.subst, type_)
  #(term, type_)
}
