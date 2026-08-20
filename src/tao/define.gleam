import core/ast as core
import core/context.{type Context}
import core/eval.{eval}
import core/format
import core/infer.{check, infer}
import core/resolve
import core/unify.{unify}
import core/value as v
import filepath
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import syntax/span.{Span}
import tao/ast.{type Module, type Stmt, type Type} as tao
import tao/declare.{type ModName, type Name}
import tao/desugar.{type BlockCtx}
import utils/list_utils

pub fn types(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> Context {
  todo
}

pub fn modules(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mods: List(Module),
) -> Context {
  todo
}

pub fn signature(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
) -> #(v.Value, v.Type, Context) {
  case get_var(ctx, mod_name, name) {
    Some(#(val, typ)) -> #(val, typ, ctx)
    None ->
      case list.key_find(defs, mod_name) {
        Error(Nil) -> {
          echo mod_name
          todo as "error: module not found"
        }
        Ok(mod_defs) ->
          case list.key_find(mod_defs, name) {
            Error(Nil) -> {
              echo #(mod_name, name)
              todo as "error: definition not found"
            }
            Ok(stmt) -> statement(ctx, defs, mod_name, name, stmt)
          }
      }
  }
}

pub fn statement(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  stmt: Stmt,
) -> #(v.Value, v.Type, Context) {
  case stmt.data {
    tao.Import(path, opt_alias, names) -> {
      let alias = case opt_alias {
        Some(alias) -> alias
        None -> filepath.base_name(path)
      }
      let names =
        list.map(names, fn(entry) {
          let #(name, opt_alias) = entry
          let alias = case opt_alias {
            Some(alias) -> alias
            None -> name
          }
          #(name, alias)
        })
      let import_stmt = #(path, alias, names)
      stmt_type_import(ctx, defs, mod_name, name, import_stmt)
    }
    tao.ImportAll(path, alias) -> todo
    tao.Extern(name, params, returns) -> todo
    tao.LetVar(_, None, _) -> {
      let #(val, ctx) = hole_value(ctx)
      let #(typ, ctx) = hole_value(ctx)
      let ctx = set_var(ctx, mod_name, name, val, typ)
      #(val, typ, ctx)
    }
    tao.LetVar(_, Some(typ), _) -> {
      let #(val, ctx) = hole_value(ctx)
      let #(typ, ctx) = expr_value(ctx, defs, mod_name, typ)
      let ctx = set_var(ctx, mod_name, name, val, typ)
      #(val, typ, ctx)
    }
    tao.LetPat(pattern, types, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.Test(name, expr, expect) -> todo
    tao.FnDef(name, implicits, params, returns, body) -> todo
    tao.FnOverload(name, choices) -> todo
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
}

fn stmt_type_import(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  import_stmt: #(ModName, Name, List(#(Name, Name))),
) -> #(v.Value, v.Type, Context) {
  let #(path, alias, names) = import_stmt
  case names {
    [] -> todo as "check module alias itself"
    [#(x, y), ..] if name == y -> signature(ctx, defs, path, x)
    [_, ..names] -> stmt_type_import(ctx, defs, mod_name, name, import_stmt)
  }
}

pub fn get_var(
  ctx: Context,
  mod_name: ModName,
  name: Name,
) -> Option(#(v.Value, v.Type)) {
  case context.lookup_var(ctx, mod_name) {
    Some(#(v.Rcd(mod_values, None), v.Rcd(mod_types, None))) -> {
      case list.key_find(mod_values, name), list.key_find(mod_types, name) {
        Ok(#(val, _)), Ok(#(typ, _)) -> Some(#(val, typ))
        _, _ -> None
      }
    }
    _ -> None
  }
}

pub fn set_var(
  ctx: Context,
  mod_name: ModName,
  name: Name,
  val: v.Value,
  typ: v.Type,
) -> Context {
  let #(mod_val, mod_typ) = case context.lookup_var(ctx, mod_name) {
    Some(#(v.Rcd(values, None), v.Rcd(types, None))) -> #(
      v.Rcd(list_utils.set(values, name, #(val, None)), None),
      v.Rcd(list_utils.set(types, name, #(typ, None)), None),
    )
    _ -> #(v.rcd([#(name, val)]), v.rcd([#(name, typ)]))
  }
  context.set_var(ctx, mod_name, mod_val, mod_typ)
}

pub fn get_mod_vars(
  ctx: Context,
  mod_name: ModName,
) -> List(#(Name, Option(v.Value), Option(v.Type))) {
  todo
}

fn hole_value(ctx: Context) -> #(v.Value, Context) {
  let #(id, ctx) = context.new_hole(ctx)
  #(v.hole(ctx.env, id), ctx)
}

fn expr_value(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  expr: tao.Expr,
) -> #(v.Value, Context) {
  let exports = declare.exports(defs)
  let core_expr = desugar.expr(exports, expr)
  let deps = core.free_vars(core_expr)
  let ctx =
    list.fold(deps, ctx, fn(ctx, name) {
      let #(val, typ, ctx) = signature(ctx, defs, mod_name, name)
      context.push_var(ctx, #(name, val, typ))
    })
  let #(term, _, ctx) = infer(ctx, core_expr)
  let value = eval(ctx.ffi, ctx.env, term)
  let ctx = context.pop_vars(ctx, list.length(deps))
  #(value, ctx)
}
// pub fn package(
//   ctx: Context,
//   defs: List(#(ModName, Declarations)),
//   mods: List(Module),
// ) -> Context {
//   let exports = declare.exports(defs)
//   let ctx = skeletons(ctx, defs, exports)
//   list.fold(mods, ctx, fn(ctx, mod) { module(ctx, exports, mod) })

//   // DELETE ME
//   // let ctx = resolve.context(ctx)
//   case ctx.errors {
//     [] -> Nil
//     _ -> {
//       echo ctx.errors
//       panic
//     }
//   }
//   list.map(list.zip(ctx.types, ctx.env), fn(entry) {
//     let names = list.map(ctx.types, fn(x) { x.0 })
//     let #(#(name, mod_type), mod_value) = entry
//     io.print("ctx.env[" <> string.inspect(name) <> "]: ")
//     io.println(format.value(ctx.ffi, names, mod_value, 80, 2))
//     io.print("ctx.types[" <> string.inspect(name) <> "]: ")
//     io.println(format.value(ctx.ffi, names, mod_type, 80, 2))
//     io.println("")
//   })
//   todo
// }

// fn skeletons(
//   ctx: Context,
//   defs: List(#(ModName, Declarations)),
//   exports: List(#(ModName, List(Name))),
// ) -> Context {
//   list.fold(defs, ctx, fn(ctx, def) {
//     let #(mod_name, declarations) = def
//     list.fold(declarations, ctx, fn(ctx, declaration) {
//       let #(name, #(stmt, opt_tao_type)) = declaration
//       let #(value_id, ctx) = context.new_hole(ctx)
//       let value = v.hole(ctx.env, value_id)
//       case stmt.data, opt_tao_type {
//         tao.Extern(..), _ -> ctx
//         _, Some(tao_type) -> {
//           let core_type_expr = desugar.expr(exports, tao_type)
//           let deps = core.free_vars(core_type_expr)
//           // TODO: define dependencies first
//           assert deps == []
//           let #(core_type_term, _, ctx) = infer(ctx, core_type_expr)
//           let core_type = eval(ctx.ffi, ctx.env, core_type_term)
//           push(ctx, mod_name, name, value, core_type)
//         }
//         _, None -> {
//           let #(type_id, ctx) = context.new_hole(ctx)
//           push(ctx, mod_name, name, value, v.hole(ctx.env, type_id))
//         }
//       }
//     })
//   })
// }

// fn push(
//   ctx: Context,
//   mod_name: ModName,
//   name: Name,
//   value: v.Value,
//   typ: v.Type,
// ) -> Context {
//   let #(mod_val, mod_typ) = case context.lookup_var(ctx, mod_name) {
//     Some(#(v.Rcd(values, None), v.Rcd(types, None))) -> #(
//       v.Rcd(list_utils.set(values, name, #(value, None)), None),
//       v.Rcd(list_utils.set(types, name, #(typ, None)), None),
//     )
//     _ -> #(v.rcd([#(name, value)]), v.rcd([#(name, typ)]))
//   }
//   context.set_var(ctx, mod_name, mod_val, mod_typ)
// }

// pub fn module(
//   ctx: Context,
//   exports: List(#(String, List(String))),
//   mod: Module,
// ) -> Context {
//   let #(mod_name, stmts) = mod
//   let mod_expr = desugar.module(exports, mod)
//   let mod_type =
//     list.key_find(ctx.types, mod_name)
//     |> result.unwrap(v.hole_open(ctx.env, None))
//   let s = Span(mod_name, 0, 0, 0, 0)
//   let #(mod_term, _, ctx) = check(ctx, mod_expr, #(mod_type, s))
//   let mod_val = eval(ctx.ffi, ctx.env, mod_term)
//   case context.lookup(ctx, mod_name) {
//     Some(#(mod_idx, _)) ->
//       case list_utils.at(ctx.env, mod_idx) {
//         Some(mod_decl) -> unify(ctx, #(mod_decl, s), #(mod_val, s))
//         None -> panic as "module not found"
//       }
//     None -> panic as "module not declared"
//   }
// }
