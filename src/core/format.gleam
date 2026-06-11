import core/ast.{type AST}
import core/literals as lit
import gleam/float
import gleam/int

pub fn format(ast: AST) -> String {
  case ast.data {
    ast.Typ(u) -> todo
    ast.Hole(id) if id < 0 -> "?"
    ast.Hole(id) -> "?<" <> int.to_string(id) <> ">"
    ast.Lit(lit) ->
      case lit {
        lit.Int(value) -> int.to_string(value)
        lit.Float(value) -> float.to_string(value)
      }
    ast.LitT(lit_t) ->
      case lit_t {
        lit.IntT -> "%Int"
        lit.FloatT -> "%Float"
        lit.I8 -> "%I8"
        lit.I16 -> "%I16"
        lit.I32 -> "%I32"
        lit.I64 -> "%I64"
        lit.U8 -> "%U8"
        lit.U16 -> "%U16"
        lit.U32 -> "%U32"
        lit.U64 -> "%U64"
        lit.F16 -> "%F16"
        lit.F32 -> "%F32"
        lit.F64 -> "%F64"
      }
    ast.Var(name) -> name
    ast.Ctr(tag, arg) -> todo
    ast.Rcd(fields) -> todo
    ast.RcdT(fields) -> todo
    ast.Ann(ast, type_) -> todo
    ast.Lam(implicit, #(name, type_), body) -> {
      let #(open, close) = case implicit {
        True -> #("<", ">")
        False -> #("(", ")")
      }
      let param = open <> name <> ": " <> format(type_) <> close
      "%fn" <> param <> " => " <> format(body)
    }
    ast.Pi(implicit, #(name, type_), codomain) -> {
      let #(open, close) = case implicit {
        True -> #("<", ">")
        False -> #("(", ")")
      }
      let domain = open <> name <> ": " <> format(type_) <> close
      "%pi" <> domain <> " -> " <> format(codomain)
    }
    ast.Fix(name, body) -> todo
    ast.App(implicit, fun, arg) -> todo
    ast.TypeDef(type_def) -> todo
    ast.Let(def, body) -> todo
    ast.Match(arg, cases) -> todo
    ast.Call(name, args, return_type) -> todo
    ast.Err -> todo
  }
}
