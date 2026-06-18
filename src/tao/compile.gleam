import core/ast as core
import core/context.{type Context}
import core/ffi.{type FFI}
import core/infer.{infer}
import core/term.{type Term}
import core/value.{type Env, type Type} as v
import gleam/list
import gleam/option.{None, Some}
import gleam/string
import syntax/span.{Span}
import tao/ast.{type Block, type Module, type Stmt} as tao
import tao/desugar.{new_block_ctx, statement_list}

pub fn package(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, #(Term, Type))), Context) {
  let core_mods = list.map(mods, desugar.module)
  let mod_vars =
    list.index_map(mods, fn(mod, index) {
      let #(name, _) = mod
      #("@" <> name, Some(v.var(index)), None)
    })
  let ctx = context.push_var_list(ctx, mod_vars)
  // todo as "add each module into the ctx with context.push_var_list"
  // todo as "for each module, compile_module"
  todo
}
