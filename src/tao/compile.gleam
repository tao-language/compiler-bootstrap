import core/ast as core
import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{check}
import core/quote.{quote}
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
import tao/tests.{type TestDef, TestDef}
import utils/list_utils

pub fn modules(ctx: Context, mods: List(Module)) -> Context {
  let defs = declare.modules(mods)
  let ctx = define.types(ctx, defs)
  let ctx = define.values(ctx, defs)
  resolve.context(ctx)
}

pub fn tests(ctx: Context, mods: List(Module)) -> List(TestDef) {
  list.flat_map(mods, fn(mod) {
    let #(mod_name, stmts) = mod
    list.filter_map(stmts, fn(stmt) {
      case stmt.data {
        tao.Test(name, expr, expect) ->
          case define.get_var(ctx, mod_name, name) {
            Some(#(value, _)) -> {
              let term = quote(ctx.ffi, list.length(ctx.env), value)
              Ok(TestDef(name, term, expr, expect))
            }
            None -> Error(Nil)
          }
        _ -> Error(Nil)
      }
    })
  })
}
