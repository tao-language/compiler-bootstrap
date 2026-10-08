import gleam/io
import gleam/list
import gleam/string
import tao/ast.{type Module} as tao

pub fn module_trace(mods: List(Module), defs: List(#(String, List(#(String, tao.Stmt))))) -> Nil {
  io.println(module_trace_string(mods, defs))
}

pub fn module_trace_string(
  mods: List(Module),
  _defs: List(#(String, List(#(String, tao.Stmt)))),
) -> String {
  let names = list.map(mods, fn(mod) { mod.0 })
  let name_lines =
    list.map(names, fn(n) { "  " <> n })
    |> string.join("\n")
  let edge_lines =
    list.map(mods, fn(mod) {
      let #(name, stmts) = mod
      list.filter(stmts, fn(stmt) {
        case stmt.data {
          tao.Import(..) -> True
          _ -> False
        }
      })
      |> list.map(fn(stmt) {
        case stmt.data {
          tao.Import(path, alias, _) ->
            "  " <> name <> " → " <> path <> " (alias: " <> alias <> ")"
          _ -> ""
        }
      })
    })
    |> list.flatten
    |> string.join("\n")
  "---- MODULE TRACE ----\nModules:\n" <> name_lines
    <> "\n\nImport edges:\n"
    <> edge_lines
    <> "\n---- END MODULE TRACE ----"
}
