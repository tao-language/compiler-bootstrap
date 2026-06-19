import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{infer}
import core/quote.{quote}
import core/resolve
import core/term.{type Term}
import core/value.{type Type} as v
import gleam/list
import gleam/option.{Some}
import tao/ast.{type Module, type Stmt}
import tao/desugar

pub fn package(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, #(Term, Type))), Context) {
  let #(pkg_mods, ctx) = define_modules(ctx, mods)
  let #(typed_mods, ctx) = infer_modules(ctx, pkg_mods)
  let typed_mods = resolve_modules(ctx, typed_mods)
  #(typed_mods, ctx)
}

fn define_modules(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, Int, Int, List(Stmt))), Context) {
  case mods {
    [] -> #([], ctx)
    [#(name, stmts), ..mods] -> {
      let #(value_id, ctx) = context.new_hole(ctx)
      let #(type_id, ctx) = context.new_hole(ctx)
      let var = #("@" <> name, Some(v.hole(value_id)), Some(v.hole(type_id)))
      let ctx = context.push_var(ctx, var)
      let #(core_mods, ctx) = define_modules(ctx, mods)
      #([#(name, value_id, type_id, stmts), ..core_mods], ctx)
    }
  }
}

fn infer_modules(
  ctx: Context,
  pkg_mods: List(#(String, Int, Int, List(Stmt))),
) -> #(List(#(String, #(Term, Type))), Context) {
  case pkg_mods {
    [] -> #([], ctx)
    [#(name, value_id, type_id, stmts), ..core_mods] -> {
      let core_expr = desugar.module(#(name, stmts))
      let #(term, type_, ctx) = infer(ctx, core_expr)
      let ctx =
        Context(..ctx, subst: [
          #(value_id, eval(ctx.ffi, ctx.env, term)),
          #(type_id, type_),
          ..ctx.subst
        ])
      let #(typed_mods, ctx) = infer_modules(ctx, core_mods)
      #([#(name, #(term, type_)), ..typed_mods], ctx)
    }
  }
}

fn resolve_modules(
  ctx: Context,
  typed_mods: List(#(String, #(Term, Type))),
) -> List(#(String, #(Term, Type))) {
  list.map(typed_mods, fn(tmod) {
    let #(name, #(term, type_)) = tmod
    let term = resolve.resolve(ctx.ffi, ctx.subst, list.length(ctx.env), term)
    let type_ = resolve.resolve_value(ctx.ffi, ctx.subst, ctx.env, type_)
    #(name, #(term, type_))
  })
}
