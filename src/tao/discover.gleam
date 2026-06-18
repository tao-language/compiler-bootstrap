import gleam/list
import tao/ast.{type Pattern, type Stmt} as tao

pub fn definitions(stmts: List(Stmt)) -> List(String) {
  list.flat_map(stmts, definitions_stmt)
}

fn definitions_stmt(stmt: Stmt) -> List(String) {
  case stmt.data {
    tao.Import(_, _, _) -> []
    tao.Let(pattern, _, _) -> definitions_pattern(pattern)
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

fn definitions_pattern(pattern: Pattern) -> List(String) {
  case pattern.data {
    tao.PAny -> []
    tao.PVar(name) -> [name]
    tao.PLit(_) -> []
    tao.PLitT(_) -> []
    tao.PRcd(fields) -> todo
    tao.PRcdT(fields) -> todo
    tao.PCtr(_, args) -> todo
  }
}

pub fn tests(stmts: List(Stmt)) -> List(String) {
  todo
}
