import core/context.{type Context}
import core/quote.{quote}
import core/resolve
import gleam/list
import gleam/option.{None}
import tao/ast.{type Module} as tao
import tao/declare
import tao/define
import tao/tests.{type TestDef, TestDef}

/// Compile a set of modules: declare, define (both phases), and resolve
/// all holes. The resulting context's errors hold any type errors.
pub fn modules(ctx: Context, mods: List(Module)) -> Context {
  let defs = declare.modules(mods)
  let ctx = define.types(ctx, defs)
  let ctx = define.values(ctx, defs)
  resolve.context(ctx)
}

/// Extract and type-check the `>>> test` statements from modules, each
/// reduced to a term that evaluates to a `Pass` or `Fail` constructor.
pub fn tests(ctx: Context, mods: List(Module)) -> #(List(TestDef), Context) {
  let defs = declare.modules(mods)
  let #(raw, ctx) =
    list.fold(mods, #([], ctx), fn(acc, mod) {
      let #(raw, ctx) = acc
      let #(mod_name, stmts) = mod
      let #(raw, ctx) =
        list.fold(stmts, #(raw, ctx), fn(acc, stmt) {
          let #(raw, ctx) = acc
          case stmt.data {
            tao.Test(name, expr, expect) -> {
              let #(value, _, ctx) =
                define.stmt_value(ctx, defs, mod_name, name, stmt, None)
              let size = list.length(ctx.env)
              let term = quote(ctx.ffi, size, value)
              let term = resolve.term(ctx.ffi, ctx.subst, size, term)
              #([TestDef(name, term, expr, expect), ..raw], ctx)
            }
            _ -> acc
          }
        })
      #(raw, ctx)
    })
  #(list.reverse(raw), ctx)
}
