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
import tao/desugar.{desugar_stmt_list, new_block_ctx}
import tao/discover

pub fn package(ctx: Context, mods: List(Module)) {
  todo as "add each module into the ctx with context.push_var_list"
  todo as "for each module, compile_module"
}

pub fn module(ctx: Context, mod: Module) -> #(Term, Type, Context) {
  let #(name, stmts) = mod
  let s = Span(name, 0, 0, 0, 0)
  let exports =
    discover.definitions(stmts)
    |> list.filter(fn(name) { !string.starts_with(name, "_") })
  let expr = desugar_stmt_list(new_block_ctx, stmts, core.rcd_vars(exports, s))
  infer(ctx, expr)
}
