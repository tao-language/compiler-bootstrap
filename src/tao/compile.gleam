import core/ast as core
import core/context.{type Context}
import core/ffi.{type FFI}
import core/value.{type Env} as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast.{type Block, type Module, type Stmt} as tao
import tao/desugar.{desugar_stmt_list, new_block_ctx}
import tao/discover

pub fn compile_package(ctx: Context, modules: List(Module)) {
  todo as "add each module into the ctx with context.push_var_list"
  todo as "for each module, compile_module"
}

pub fn compile_module(ctx: Context, module: Module) -> #(String, core.Expr) {
  let #(name, stmts) = module
  let s = Span(name, 0, 0, 0, 0)
  let exports = discover.definitions_public(stmts)
  let asdf = desugar_stmt_list(new_block_ctx, stmts, core.rcd_vars(exports, s))
  todo
}
