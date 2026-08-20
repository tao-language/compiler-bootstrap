import filepath
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import syntax/span.{type Span}
import tao/ast.{type Module, type Stmt} as tao

pub type ModName =
  String

pub type Name =
  String

pub fn modules(mods: List(Module)) -> List(#(ModName, List(#(Name, Stmt)))) {
  case mods {
    [] -> []
    [#(mod_name, stmts), ..mods] -> {
      let mod_defs = list.flat_map(stmts, statement)
      [#(mod_name, mod_defs), ..modules(mods)]
    }
  }
}

pub fn statement(stmt: Stmt) -> List(#(Name, Stmt)) {
  case stmt.data {
    tao.Import(path, alias, names) -> todo
    tao.ImportAll(path, alias) -> todo
    tao.Extern(name, params, returns) -> todo
    tao.LetVar(name, opt_type, value) -> [#(name, stmt)]
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

pub fn exports(
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> List(#(ModName, List(Name))) {
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    #(mod_name, list.map(mod_defs, fn(def) { def.0 }))
  })
}
