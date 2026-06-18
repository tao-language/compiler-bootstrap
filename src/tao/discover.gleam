import gleam/list
import gleam/string
import tao/ast.{type Stmt}

pub fn definitions(stmts: List(Stmt)) -> List(String) {
  todo
}

pub fn definitions_public(stmts: List(Stmt)) -> List(String) {
  definitions(stmts)
  |> list.filter(fn(name) { !string.starts_with(name, "_") })
}

pub fn tests(stmts: List(Stmt)) -> List(String) {
  todo
}
