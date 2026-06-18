import gleam/list
import tao/ast.{type Stmt} as tao

pub fn definitions(stmts: List(Stmt)) -> List(String) {
  list.flat_map(stmts, definitions_stmt)
}

fn definitions_stmt(stmt: Stmt) -> List(String) {
  case stmt.data {
    tao.Let(pattern, opt_type, value) -> todo
    tao.LetMut(name, opt_type, value) -> todo
    tao.Mut(name, value) -> todo
    tao.FnDef(name, implicits, params, returns, body) -> todo
    tao.TypeDef(type_def) -> todo
    tao.For(iterator, range, body) -> todo
    tao.While(condition, body) -> todo
    tao.Return(expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
}

pub fn tests(stmts: List(Stmt)) -> List(String) {
  todo
}
