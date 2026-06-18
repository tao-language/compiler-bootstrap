import core/ast as core
import core/context.{type Context}
import core/ffi.{type FFI}
import core/value.{type Env} as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast.{type Block, type Stmt} as tao
import tao/desugar.{desugar_stmt_list, new_block_ctx}
import tao/discover

pub fn compile(ctx: Context, modules: List(#(String, List(Stmt)))) -> Context {
  let #(mod_holes, ctx) = module_holes(ctx, modules)
  let namespace = modules_stmt(mod_holes)
  let asdf =
    list.map(modules, fn(mod) {
      let #(name, stmts) = mod
      compile_module(#(name, [namespace, ..stmts]))
    })
  todo
}

pub fn compile_module(module: #(String, List(Stmt))) {
  let #(name, stmts) = module
  let s = Span(name, 0, 0, 0, 0)
  let exports = discover.definitions_public(stmts)
  let asdf = desugar_stmt_list(new_block_ctx, stmts, core.rcd_vars(exports, s))
  todo
}

fn module_holes(
  ctx: Context,
  modules: List(#(String, Block)),
) -> #(List(#(String, Int)), Context) {
  case modules {
    [] -> #([], ctx)
    [#(name, _), ..modules] -> {
      let #(id, ctx) = context.new_hole(ctx)
      let #(holes, ctx) = module_holes(ctx, modules)
      #([#(name, id), ..holes], ctx)
    }
  }
}

fn modules_stmt(mod_holes: List(#(String, Int))) -> Stmt {
  let s = Span("<tao.compile.modules>", 0, 0, 0, 0)
  let pfields =
    list.map(mod_holes, fn(kv) {
      let #(name, _) = kv
      #(name, tao.pvar(name, s))
    })
  let vfields =
    list.map(mod_holes, fn(kv) {
      let #(name, id) = kv
      #(name, tao.hole(Some(id), s))
    })
  tao.let_(tao.prcd(pfields, s), None, tao.rcd(vfields, s), s)
}
