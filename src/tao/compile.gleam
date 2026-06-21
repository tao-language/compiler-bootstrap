import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{infer}
import core/resolve
import core/term.{type Term} as tm
import core/value as v
import gleam/list
import gleam/option.{Some}
import gleam/string
import tao/ast.{type Expr, type Module, type Pattern, type Stmt}
import tao/desugar
import tao/discover

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  let #(mod_holes, ctx) = define_modules(ctx, mods)
  let ctx = infer_modules(ctx, mod_holes)
  resolve.context(ctx)
}

pub fn tests(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, Term, Expr, Pattern)), Context) {
  case mods {
    [] -> #([], ctx)
    [#(name, stmts), ..mods] -> {
      let test_defs = discover.tests(stmts)
      let test_names = list.map(test_defs, fn(tst) { "> " <> tst.0 })
      let mod_expr = desugar.module(#(name, stmts), test_names)
      let #(mod_term, _, ctx) = infer(ctx, mod_expr)
      let mod_tests =
        list.map(test_defs, fn(tst) {
          let #(name, expr, expect) = tst
          #(name, tm.dot(mod_term, "> " <> tst.0), expr, expect)
        })
      let #(tail_tests, ctx) = tests(ctx, mods)
      #(list.append(mod_tests, tail_tests), ctx)
    }
  }
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
        |> list.filter(fn(name) { !string.starts_with(name, "_") })
        |> desugar.module(#(name, stmts), _)
      let #(defs_term, defs_type, ctx) = infer(ctx, mod_expr)
      let ctx =
        Context(..ctx, subst: [
          #(value_id, eval(ctx.ffi, ctx.env, defs_term)),
          #(type_id, defs_type),
          ..ctx.subst
        ])
      infer_modules(ctx, mod_holes)
    }
  }
}
