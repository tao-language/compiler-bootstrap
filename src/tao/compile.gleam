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
import tao/tests.{type TestDef, TestDef}
import utils/list_utils

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  // let defs = declare.modules(mods)
  // define.modules(ctx, defs)
  todo
}

pub fn tests(ctx: Context, mods: List(Module)) -> List(TestDef) {
  // list.flat_map(mods, fn(mod) {
  //   let #(mod_name, stmts) = mod
  //   let mod_tests = discover.tests(stmts)
  //   list.map(mod_tests, fn(t) {
  //     let #(test_name, expr, expect) = t
  //     let mod_index = case context.lookup(ctx, mod_name) {
  //       Some(#(mod_index, _)) -> mod_index
  //       None -> {
  //         echo mod_name
  //         echo list.map(ctx.types, fn(x) { x.0 })
  //         panic as "test module not in context"
  //       }
  //     }
  //     let term = tm.dot(tm.Var(mod_index), test_name)
  //     TestDef(test_name, term, expr, expect)
  //   })
  // })
  todo
}
