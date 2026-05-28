import core/ast
import core/state.{type FFI}
import core/utils
import gleam/list
import gleam/option.{None, Some}

pub fn eval(ffi: FFI, env: ast.Env, term: ast.Term) -> ast.Value {
  case term {
    ast.Typ(universe, _) -> ast.VTyp(universe)
    ast.Hole(id, _) -> ast.vhole(id)
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
      let result = case list.key_find(ffi, name) {
        Ok(call) -> call(args_val)
        Error(Nil) -> None
      }
      case result {
        Some(value) -> value
        None -> ast.vcall(name, args_val)
      }
    }
    ast.Ann(term, _, _) -> eval(ffi, env, term)
    ast.Lam(implicit, #(name, param), body, _) -> {
      let param_val = eval(ffi, env, param)
      ast.VLam(implicit, #(name, param_val), #(env, body))
    }
    ast.Pi(implicit, #(name, domain), codomain, _) -> {
      let domain_val = eval(ffi, env, domain)
      ast.VPi(implicit, #(name, domain_val), #(env, codomain))
    }
    ast.Fix(name, body, _) -> ast.VFix(name, #(env, body))
    ast.App(fun, arg, _) -> {
      let fun_val = eval(ffi, env, fun)
      let arg_val = eval(ffi, env, arg)
      do_app(ffi, fun_val, arg_val)
    }
    ast.Union(variants, _) -> {
      todo
    }
    ast.Match(arg, cases, _) -> {
      let arg_val = eval(ffi, env, arg)
      do_match(ffi, env, arg_val, cases)
    }
    ast.Err(_) -> ast.VErr
  }
}

fn do_app(ffi: FFI, fun: ast.Value, arg: ast.Value) -> ast.Value {
  case fun {
    // Neutral application
    ast.VNeut(neut_fun) -> ast.vapp(neut_fun, arg)
    // Explicit parameter: β-reduction
    ast.VLam(False, _, #(env, body)) -> eval(ffi, [arg, ..env], body)
    // Implicit parameter: implicit expansion
    ast.VLam(True, param, #(env, body)) -> {
      // Implicit parameters are expanded and solved during elaboration,
      // expand into an error since there's no additional information.
      let fun = ast.VLam(False, param, #([ast.VErr, ..env], body))
      do_app(ffi, do_app(ffi, fun, ast.VErr), arg)
    }
    _ -> ast.VErr
  }
}

fn do_match(
  ffi: FFI,
  env: ast.Env,
  arg: ast.Value,
  cases: List(ast.Case),
) -> ast.Value {
  todo
}
