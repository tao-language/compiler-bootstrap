import gleam/list
import tao/ast.{type Module, type Stmt} as tao

pub type ModName =
  String

pub type Name =
  String

/// Collect all module definitions and expand imports into the full
/// definition list, so every name maps to the statement that defines it.
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

/// The names a statement introduces in its module (imports introduce
/// many; tests introduce none).
pub fn statement(stmt: Stmt) -> List(#(Name, Stmt)) {
  case stmt.data {
    tao.Import(_, alias, tao.ImportAll) -> [#(alias, stmt)]
    tao.Import(_, alias, tao.ImportSome(names)) -> [
      #(alias, stmt),
      ..list.map(names, fn(x) { #(x.1, stmt) })
    ]
    tao.Extern(name, _params, _returns) -> [#(name, stmt)]
    tao.LetVar(name, _opt_type, _value) -> [#(name, stmt)]
    tao.LetPat(_pattern, _types, _value) -> todo
    tao.LetMut(_name, _opt_type, _value) -> todo
    tao.Mut(_name, _value) -> todo
    tao.Test(_name, _, _) -> []
    tao.FnDef(name, ..) -> [#(name, stmt)]
    tao.FnOverload(name, _) -> [#(name, stmt)]
    tao.TypeDef(name, _) -> [#(name, stmt)]
    tao.For(_iterator, _range, _body) -> todo
    tao.While(_condition, _body) -> todo
    tao.Return(_expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
}

/// Expand `import` statements: every name introduced by an import maps
/// to the *import* statement, so looking the name up later re-runs the
/// import's desugaring.
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
                list.filter(import_defs, fn(mod_def) {
                  is_public_name(mod_def.0)
                })
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

/// For each module, the list of names it defines (used for module
/// records and import scopes).
pub fn exports(
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> List(#(ModName, List(Name))) {
  list.map(defs, fn(def) {
    let #(mod_name, mod_defs) = def
    #(mod_name, list.map(mod_defs, fn(def) { def.0 }))
  })
}

/// A name is importable from a module. Externs (`@…`) and tests
/// (`>>> …`) are not importable. Underscore names (`_…`, e.g. the
/// prelude's `_or`) *are* importable: the prelude exposes them to every
/// module via the implicit prelude import, and user modules may expose
/// them the same way. (Cross-package restriction is a planned
/// post-process, not enforced yet.)
pub fn is_public_name(name: String) -> Bool {
  case name {
    "@" <> _ -> False
    ">>> " <> _ -> False
    _ -> True
  }
}
