import core/ast.{type AST, AST} as core
import tao/ast.{type Expr} as tao

pub fn desugar_expr(expr: Expr) -> AST {
  let data = case expr.data {
    tao.Hole(id) -> core.Hole(id)
    tao.Lit(value) -> core.Lit(value)
    tao.Var(name) -> core.Var(name)
    tao.Ctr(tag, args) -> todo
    tao.Rcd(fields) -> todo
    tao.RcdT(fields) -> todo
    tao.Ann(value, type_) -> todo
    tao.Fn(implicits, params, body) -> todo
    tao.FnT(implicits, params, body) -> todo
    tao.App(fun, implicits, args) -> todo
    tao.TypeDef(type_def) -> todo
    tao.Match(arg, cases) -> todo
    tao.Call(name, ret, args) -> todo
    tao.Let(def, body) -> todo
    tao.Err -> core.Err
  }
  AST(data, expr.span)
}
