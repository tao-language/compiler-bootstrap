import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{infer}
import core/quote.{quote}
import core/resolve
import core/term.{type Term}
import core/value.{type Env, type Type} as v
import gleam/list
import gleam/option.{Some}
import tao/ast.{type Module, type Stmt}
import tao/desugar

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  let #(mod_holes, ctx) = define_modules(ctx, mods)
  let ctx = infer_modules(ctx, mod_holes)
  resolve.context(ctx)
}

fn define_modules(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, Int, Int, List(Stmt))), Context) {
  case mods {
    [] -> #([], ctx)
    [#(name, stmts), ..mods] -> {
      let #(core_mods, ctx) = define_modules(ctx, mods)
      let #(value_id, ctx) = context.new_hole(ctx)
      let #(type_id, ctx) = context.new_hole(ctx)
      let var = #("@" <> name, Some(v.hole(value_id)), Some(v.hole(type_id)))
      let ctx = context.push_var(ctx, var)
      #([#(name, value_id, type_id, stmts), ..core_mods], ctx)
    }
  }
}

fn infer_modules(
  ctx: Context,
  mod_holes: List(#(String, Int, Int, List(Stmt))),
) -> Context {
  case mod_holes {
    [] -> ctx
    [#(name, value_id, type_id, stmts), ..core_mods] -> {
      let core_expr = desugar.module(#(name, stmts))
      let #(term, type_, ctx) = infer(ctx, core_expr)
      let ctx =
        Context(..ctx, subst: [
          #(value_id, eval(ctx.ffi, ctx.env, term)),
          #(type_id, type_),
          ..ctx.subst
        ])
      infer_modules(ctx, core_mods)
    }
  }
}
