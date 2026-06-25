import core/ast as core
import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{check, infer}
import core/resolve
import core/term.{type Term} as tm
import core/value as v
import gleam/list
import gleam/option.{Some}
import gleam/string
import syntax/span.{Span}
import tao/ast.{type Expr, type Module, type Pattern, type Stmt}
import tao/desugar
import tao/discover
import tao/tests.{type TestDef, TestDef}

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  let #(mod_holes, ctx) = define_modules(ctx, mods)
  let ctx = infer_modules(ctx, mod_holes)
  resolve.context(ctx)
}

pub fn tests(mods: List(Module)) -> List(TestDef) {
  list.index_map(mods, fn(mod, mod_index) {
    let #(_, stmts) = mod
    let tm_mod = tm.Var(mod_index)
    let mod_tests = discover.tests(stmts)
    list.map(mod_tests, fn(t) {
      let #(test_name, expr, expect) = t
      TestDef(test_name, tm.dot(tm_mod, "> " <> test_name), expr, expect)
    })
  })
  |> list.flatten
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
    [#(name, value_id, type_id, stmts), ..mod_holes] -> {
      let mod_expr =
        discover.definitions(stmts)
        |> desugar.module(#(name, stmts), _)
      let #(defs_term, _, ctx) =
        check(ctx, mod_expr, #(v.hole(type_id), mod_expr.span))
      let ctx =
        Context(..ctx, subst: [
          #(value_id, eval(ctx.ffi, ctx.env, defs_term)),
          ..ctx.subst
        ])
      infer_modules(ctx, mod_holes)
    }
  }
}
