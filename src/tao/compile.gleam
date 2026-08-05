import core/ast as core
import core/context.{type Context, Context}
import core/eval.{eval}
import core/infer.{check}
import core/resolve
import core/term as tm
import core/unify.{unify}
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import gleam/result
import syntax/span.{type Span, Span}
import tao/ast.{type Module, type Stmt} as tao
import tao/desugar
import tao/discover
import tao/tests.{type TestDef, TestDef}
import utils/list_utils

pub fn package(ctx: Context, mods: List(Module)) -> Context {
  let #(exports, ctx) = declarations(ctx, mods)
  let ctx = definitions(ctx, exports, mods)
  resolve.context(ctx)
}

pub fn declarations(
  ctx: Context,
  mods: List(Module),
) -> #(List(#(String, List(String))), Context) {
  case mods {
    [] -> #([], ctx)
    [mod, ..mods] -> {
      let #(mod_exports, ctx) = declare_module(ctx, mod)
      let #(exports, ctx) = declarations(ctx, mods)
      #([mod_exports, ..exports], ctx)
    }
  }
}

pub fn definitions(
  ctx: Context,
  exports: List(#(String, List(String))),
  mods: List(Module),
) -> Context {
  case mods {
    [] -> ctx
    [mod, ..mods] -> {
      let ctx = define_module(ctx, exports, mod)
      definitions(ctx, exports, mods)
    }
  }
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
      let term = tm.dot(tm.Var(mod_index), ">>> " <> test_name)
      TestDef(test_name, term, expr, expect)
    })
  })
}

fn declare_module(
  ctx: Context,
  mod: Module,
) -> #(#(String, List(String)), Context) {
  let #(mod_name, stmts) = mod
  let #(values, types, ctx) = declare_stmt_list(ctx, stmts)
  let exports = list.map(values, fn(decl) { decl.0 })
  let ctx =
    context.push_var(ctx, #(mod_name, Some(v.rcd(values)), Some(v.rcd(types))))
  #(#(mod_name, exports), ctx)
}

fn declare_stmt_list(
  ctx: Context,
  stmts: List(Stmt),
) -> #(List(#(String, v.Value)), List(#(String, v.Type)), Context) {
  case stmts {
    [] -> #([], [], ctx)
    [stmt, ..stmts] -> {
      let #(values1, types1, ctx) = declare_stmt(ctx, stmt)
      let #(values2, types2, ctx) = declare_stmt_list(ctx, stmts)
      #(list.append(values1, values2), list.append(types1, types2), ctx)
    }
  }
}

fn declare_stmt(
  ctx: Context,
  stmt: Stmt,
) -> #(List(#(String, v.Value)), List(#(String, v.Type)), Context) {
  case stmt.data {
    tao.Import(..) -> #([], [], ctx)
    tao.ImportAll(..) -> #([], [], ctx)
    tao.Let(pattern, opt_type, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.Test(name, expr, expect) -> {
      let name = ">>> " <> name
      let #(value_id, ctx) = context.new_hole(ctx)
      let #(type_id, ctx) = context.new_hole(ctx)
      let value = v.hole([], value_id)
      let type_ = v.hole([], type_id)
      #([#(name, value)], [#(name, type_)], ctx)
    }
    tao.FnDef(
      name,
      implicits,
      implicits_tail,
      params,
      params_tail,
      returns,
      body,
    ) -> todo
    tao.FnOverload(name, choices) -> {
      let #(value_id, ctx) = context.new_hole(ctx)
      let #(type_id, ctx) = context.new_hole(ctx)
      let value = v.For([], #("", v.Typ(0)), tm.hole(value_id))
      let type_ = v.hole([], type_id)
      #([#(name, value)], [#(name, type_)], ctx)
    }
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
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
      case list_utils.list_at(ctx.env, mod_idx) {
        Some(mod_decl) -> unify(ctx, #(mod_decl, s), #(mod_val, s))
        None -> panic as "module not found"
      }
    None -> panic as "module not declared"
  }
}
