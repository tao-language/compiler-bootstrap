import core/error as e
import gleam/list
import gleam/string
import tao/ast.{type Module, type Stmt} as tao

pub type ModName =
  String

pub type Name =
  String

/// Collect all module definitions and expand imports into the full
/// definition list, so every name maps to the statement that defines it.
pub fn modules(
  mods: List(Module),
) -> #(List(#(ModName, List(#(Name, Stmt)))), List(e.Error)) {
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
    tao.Test(_name, _, _) ->
      // DO NOT declare tests as part of the package.
      // The whole project packages goes through NbE, which means
      // tests would run at compile time.
      // So first build/compile/NbE the project WITHOUT tests.
      // To run tests, there has to be a separate pass, see tao/compile.tests
      []
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
/// import's desugaring. Every module's imports are resolved against the
/// complete definition list, so resolution is independent of module order
/// (a module may import one that appears before or after it).
pub fn imports(
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> #(List(#(ModName, List(#(Name, Stmt)))), List(e.Error)) {
  expand_all(defs, defs)
}

fn expand_all(
  defs: List(#(ModName, List(#(Name, Stmt)))),
  all_defs: List(#(ModName, List(#(Name, Stmt)))),
) -> #(List(#(ModName, List(#(Name, Stmt)))), List(e.Error)) {
  case defs {
    [] -> #([], [])
    [#(mod_name, mod_defs), ..rest] -> {
      let #(new_defs, errs1) = expand_mod_defs(mod_defs, all_defs)
      let #(rest_defs, errs2) = expand_all(rest, all_defs)
      #(
        list.append([#(mod_name, new_defs)], rest_defs),
        list.append(errs1, errs2),
      )
    }
  }
}

fn expand_mod_defs(
  mod_defs: List(#(Name, Stmt)),
  all_defs: List(#(ModName, List(#(Name, Stmt)))),
) -> #(List(#(Name, Stmt)), List(e.Error)) {
  case mod_defs {
    [] -> #([], [])
    [#(name, stmt), ..rest] -> {
      let #(rest_defs, rest_errs) = expand_mod_defs(rest, all_defs)
      case stmt.data {
        tao.Import(path, _, tao.ImportAll) ->
          case list.key_find(all_defs, path) {
            Error(Nil) -> {
              let known = list.map(all_defs, fn(entry) { entry.0 })
              let err = e.Error(
                e.SyntaxError(
                  "module not found: " <> path
                    <> " (known: "
                    <> string.join(known, ", ")
                    <> ")",
                ),
                stmt.span,
                [],
              )
              #([#(name, stmt), ..rest_defs], [err, ..rest_errs])
            }
            Ok(import_defs) -> {
              let exposed =
                list.filter(import_defs, fn(mod_def) {
                  is_public_name(mod_def.0)
                })
                |> list.map(fn(mod_def) { #(mod_def.0, stmt) })
              let all = list.append([#(name, stmt)], exposed)
              #(list.append(all, rest_defs), rest_errs)
            }
          }
        _ -> #([#(name, stmt), ..rest_defs], rest_errs)
      }
    }
  }
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
