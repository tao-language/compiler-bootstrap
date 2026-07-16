import core/ast as core
import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{check}
import core/resolve
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{Some}
import syntax/span.{Span}
import tao/ast.{type Module, type Stmt}
import tao/desugar
import tao/discover
import tao/tests.{type TestDef, TestDef}

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  let mods_defs = definitions(mods)
  let defs = list.map(mods_defs, fn(m) { #(m.0, m.1) })
  let #(core_mods, ctx) = define_modules(ctx, defs, mods_defs)
  let ctx = infer_modules(ctx, core_mods)
  resolve.context(ctx)
}

pub fn tests(mods: List(Module)) -> List(TestDef) {
  list.index_map(mods, fn(mod, mod_index) {
    let #(_, stmts) = mod
    let mod_tests = discover.tests(stmts)
    list.map(mod_tests, fn(t) {
      let #(test_name, expr, expect) = t
      let term = tm.dot(tm.Var(mod_index), ">>> " <> test_name)
      TestDef(test_name, term, expr, expect)
    })
  })
  |> list.flatten
}

fn definitions(
  mods: List(Module),
) -> List(#(String, List(String), List(Stmt))) {
  list.map(mods, fn(mod) {
    let #(name, stmts) = mod
    #(name, discover.definitions(stmts), stmts)
  })
}

fn define_modules(
  ctx: Context,
  defs: List(#(String, List(String))),
  mods: List(#(String, List(String), List(Stmt))),
) -> #(List(#(Int, Int, core.Expr)), Context) {
  case mods {
    [] -> #([], ctx)
    [#(name, exports, stmts), ..mods] -> {
      let #(core_mods, ctx) = define_modules(ctx, defs, mods)
      let #(value_id, ctx) = context.new_hole(ctx)
      let #(type_id, ctx) = context.new_hole(ctx)
      let var = #(
        "@" <> name,
        Some(v.hole(ctx.env, Some(value_id))),
        Some(v.hole(ctx.env, Some(type_id))),
      )
      let ctx = context.push_var(ctx, var)
      let mod_expr = desugar.module(defs, exports, #(name, stmts))
      let core_mods = [#(value_id, type_id, mod_expr), ..core_mods]
      #(core_mods, ctx)
    }
  }
}

fn infer_modules(
  ctx: Context,
  core_mods: List(#(Int, Int, core.Expr)),
) -> Context {
  case core_mods {
    [] -> ctx
    [#(value_id, type_id, mod_expr), ..mod_holes] -> {
      let #(mod_term, _mod_type, ctx) =
        check(ctx, mod_expr, #(v.hole(ctx.env, Some(type_id)), mod_expr.span))
      let mod_value = eval(ctx.ffi, ctx.env, mod_term)
      let ctx = Context(..ctx, subst: [#(value_id, mod_value), ..ctx.subst])
      infer_modules(ctx, mod_holes)
    }
  }
}
