import core/ast
import core/state.{type FFI}
import core/utils
import gleam/list
import gleam/option.{None, Some}

pub fn eval(ffi: FFI, env: ast.Env, term: ast.Term) -> ast.Value {
  case term {
    ast.Typ(universe, _) -> ast.VTyp(universe)
    ast.Hole(id, _) -> ast.vhole(id, [])
    ast.Lit(value, _) -> ast.VLit(value)
    ast.LitT(value, _) -> ast.VLitT(value)
    ast.Var(index, _) ->
      case utils.list_at(env, index) {
        Some(value) -> value
        None -> ast.VErr
      }
    // Var(index: Int, span: Span)
    // Ctr(tag: String, arg: Term, span: Span)
    ast.Rcd(fields, _) ->
      ast.VRcd(
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, eval(ffi, env, term))
        }),
      )
    ast.RcdT(fields, _) ->
      ast.VRcdT(
        list.map(fields, fn(field) {
          let #(name, term, default) = field
          #(name, eval(ffi, env, term), option.map(default, eval(ffi, env, _)))
        }),
      )
    // Call(name: String, args: List(#(Term, Term)), return_type: Term, span: Span)
    // Ann(term: Term, type_: Term, span: Span)
    // Lam( implicits: List(#(String, Term)), param: #(String, Term), body: Term, span: Span, )
    // Pi( implicits: List(#(String, Term)), domain: #(String, Term), codomain: Term, span: Span, )
    // Fix(name: String, body: Term, span: Span)
    // App(fun: Term, arg: Term, span: Span)
    // TypeDef( params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )
    // Match(arg: Term, cases: List(Case), span: Span)
    // Err(message: String, span: Span)
    _ -> {
      echo term
      todo
    }
  }
}
