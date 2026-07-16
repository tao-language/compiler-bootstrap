import gleam/list
import tao/ast.{type Expr, type Pattern, type Stmt} as tao

pub fn definitions(stmts: List(Stmt)) -> List(String) {
  list.flat_map(stmts, fn(stmt) {
    case stmt.data {
      tao.Import(..) -> []
      tao.ImportAll(..) -> []
      tao.Let(pattern, ..) -> definitions_pattern(pattern)
      tao.LetMut(name, opt_type, value) -> todo
      tao.Mut(name, value) -> todo
      tao.Test(name, ..) -> [">>> " <> name]
      tao.FnDef(name, ..) -> [name]
      tao.FnOverload(name, ..) -> [name]
      tao.TypeDef(type_def) -> todo
      tao.For(iterator, range, body) -> todo
      tao.While(condition, body) -> todo
      tao.Return(expr) -> todo
      tao.Break -> todo
      tao.Continue -> todo
    }
  })
}

pub fn tests(stmts: List(Stmt)) -> List(#(String, Expr, Pattern)) {
  list.flat_map(stmts, fn(stmt) {
    case stmt.data {
      tao.Import(..) -> []
      tao.ImportAll(..) -> []
      tao.Let(..) -> []
      tao.LetMut(..) -> []
      tao.Mut(..) -> []
      tao.Test(name, expr, expect) -> [#(name, expr, expect)]
      tao.FnDef(..) -> []
      tao.FnOverload(..) -> []
      tao.TypeDef(..) -> []
      tao.For(iterator, range, body) -> todo
      tao.While(condition, body) -> todo
      tao.Return(expr) -> todo
      tao.Break -> todo
      tao.Continue -> todo
    }
  })
}

fn definitions_pattern(pattern: Pattern) -> List(String) {
  case pattern.data {
    tao.PAny -> []
    tao.PVar(name) -> [name]
    tao.PLit(_) -> []
    tao.PRcd(fields, tail) -> todo
    tao.PCtr(_, args, tail) -> todo
  }
}
