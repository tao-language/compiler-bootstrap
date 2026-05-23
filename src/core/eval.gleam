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
    ast.Ctr(tag, arg, _) -> ast.VCtr(tag, eval(ffi, env, arg))
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
    ast.Call(name, args, _, _) -> {
      let args_val = list.map(args, eval(ffi, env, _))
      let result =
        utils.list_lookup(ffi, name)
        |> option.then(fn(call) { call(args_val) })
      case result {
        Some(value) -> value
        None -> ast.vcall(name, args_val, [])
      }
    }
    ast.Ann(term, _, _) -> eval(ffi, env, term)
    ast.Lam(implicits, #(name, param_type), body, _) -> {
      todo
    }
    ast.Pi(_implicits, #(_name, _domain), _codomain, _) -> {
      // Pi types are types, so their type is $Type (VTyp(0))
      ast.VTyp(0)
    }
    ast.Fix(name, body, _) -> {
      todo
    }
    ast.App(fun, arg, _) -> {
      todo
    }
    ast.TypeDef(params, constructors, _) -> {
      todo
    }
    ast.Match(arg, cases, _) -> {
      todo
    }
    ast.Err(_) -> ast.VErr
  }
}
