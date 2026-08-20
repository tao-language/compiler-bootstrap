import core/ast as core
import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{check}
import core/resolve
import core/term as tm
import core/unify.{unify}
import core/value.{type Env} as v
import gleam/list
import gleam/option.{None, Some}
import gleam/result
import syntax/span.{type Span, Span}
import tao/ast.{type Module, type Pattern, type Stmt} as tao
import tao/declare
import tao/define
import tao/desugar
import tao/discover
import tao/tests.{type TestDef, TestDef}
import utils/list_utils

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  // let defs = declare.package(mods)
  // define.package(ctx, defs, mods)
  todo
}

pub fn tests(ctx: Context, mods: List(Module)) -> List(TestDef) {
  list.flat_map(mods, fn(mod) {
    let #(mod_name, stmts) = mod
    let mod_tests = discover.tests(stmts)
    list.map(mod_tests, fn(t) {
      let #(test_name, expr, expect) = t
      let mod_index = case context.lookup(ctx, mod_name) {
        Some(#(mod_index, _)) -> mod_index
        None -> {
          echo mod_name
          echo list.map(ctx.types, fn(x) { x.0 })
          panic as "test module not in context"
        }
      }
      let term = tm.dot(tm.Var(mod_index), test_name)
      TestDef(test_name, term, expr, expect)
    })
  })
}

fn define_module(
  ctx: Context,
  exports: List(#(String, List(String))),
  mod: Module,
) -> Context {
  let #(mod_name, stmts) = mod
  let mod_expr = desugar.module(exports, mod)
  let mod_type =
    list.key_find(ctx.types, mod_name)
    |> result.unwrap(v.hole_open(ctx.env, None))
  let s = Span(mod_name, 0, 0, 0, 0)
  let #(mod_term, mod_type, ctx) = check(ctx, mod_expr, #(mod_type, s))
  let mod_val = eval(ctx.ffi, ctx.env, mod_term)
  case context.lookup(ctx, mod_name) {
    Some(#(mod_idx, _)) ->
      case list_utils.at(ctx.env, mod_idx) {
        Some(mod_decl) -> {
          // let #(mod_decl, ctx) = concretize_holes(ctx, mod_decl)
          unify(ctx, #(mod_decl, s), #(mod_val, s))
        }
        None -> panic as "module not found"
      }
    None -> panic as "module not declared"
  }
}
