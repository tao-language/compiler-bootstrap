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
  // Build the complete defs list first, then resolve imports once against
  // it. Resolving against a partial list (e.g. from a recursive step) would
  // fail to find modules that appear later in the list, making the result
  // depend on module order.
  let defs = module_defs(mods)
  imports(defs)
}

fn module_defs(mods: List(Module)) -> List(#(ModName, List(#(Name, Stmt)))) {
  case mods {
    [] -> []
    [#(mod_name, stmts), ..mods] -> {
      let mod_defs = list.flat_map(stmts, statement)
      [#(mod_name, mod_defs), ..module_defs(mods)]
    }
  }
}

pub fn statement(stmt: Stmt) -> List(#(Name, Stmt)) {
  case stmt.data {
    tao.Import(_, alias, tao.ImportAll) -> [#(alias, stmt)]
    tao.Import(_, alias, tao.ImportSome(names)) -> [
      #(alias, stmt),
      ..list.map(names, fn(x) { #(x.1, stmt) })
    ]
    tao.Extern(name, params, returns) -> [#(name, stmt)]
    tao.LetVar(name, opt_type, value) -> [#(name, stmt)]
    tao.LetPat(pattern, types, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.Test(name, _, _) -> [#(name, stmt)]
    tao.FnDef(name, implicits, params, returns, body) -> todo
    tao.FnOverload(name, _) -> [#(name, stmt)]
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
}

pub fn imports(
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> List(#(ModName, List(#(Name, Stmt)))) {
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    let mod_defs =
      list.flat_map(mod_defs, fn(mod_def) {
        let #(name, stmt) = mod_def
        case stmt.data {
          tao.Import(path, _, tao.ImportAll) -> {
            let exposed = case list.key_find(defs, path) {
              Error(Nil) -> {
                echo path
                echo list.map(defs, fn(entry) { entry.0 })
                todo as "error: module not found"
              }
              Ok(import_defs) ->
                // Flatten only public names into the import scope, matching
                // desugar.is_public_name: non-public entries (externs, tests)
                // must not become entries of the importing module.
                list.filter(import_defs, fn(mod_def) { is_public_name(mod_def.0) })
                |> list.map(fn(mod_def) {
                  let #(name, _) = mod_def
                  #(name, stmt)
                })
            }
            [#(name, stmt), ..exposed]
          }
          _ -> [#(name, stmt)]
        }
      })
    #(mod_name, mod_defs)
  })
}

pub fn exports(
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> List(#(ModName, List(Name))) {
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    #(mod_name, list.map(mod_defs, fn(def) { def.0 }))
  })
}

/// A name is public if it can be imported from a module. Externs (`@…`),
/// private names (`_…`) and tests (`>>> …`) are not importable.
pub fn is_public_name(name: String) -> Bool {
  case name {
    "_" <> _ -> False
    "@" <> _ -> False
    ">>> " <> _ -> False
    _ -> True
  }
}
