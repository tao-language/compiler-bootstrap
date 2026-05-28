import core/ast
import core/state.{type FFI}
import core/utils
import gleam/list
import gleam/option.{None, Some}

pub fn evaluate(ffi: FFI, env: ast.Env, term: ast.Term) -> ast.Value {
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
    ast.Ctr(tag, arg, _) -> ast.VCtr(tag, evaluate(ffi, env, arg))
    ast.Rcd(fields, _) ->
      ast.VRcd(
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, evaluate(ffi, env, term))
        }),
      )
    ast.RcdT(fields, _) ->
      ast.VRcdT(
        list.map(fields, fn(field) {
          let #(name, term, default) = field
          #(
            name,
            evaluate(ffi, env, term),
            option.map(default, evaluate(ffi, env, _)),
          )
        }),
      )
    ast.Call(name, args, _, _) -> {
      let args_val = list.map(args, evaluate(ffi, env, _))
      let result = case list.key_find(ffi, name) {
        Ok(call) -> call(args_val)
        Error(Nil) -> None
      }
      case result {
        Some(value) -> value
        None -> ast.vcall(name, args_val)
      }
    }
    ast.Ann(term, _, _) -> evaluate(ffi, env, term)
    ast.Lam(implicit, #(name, param), body, _) -> {
      let param_val = evaluate(ffi, env, param)
      ast.VLam(implicit, #(name, param_val), #(env, body))
    }
    ast.Pi(implicit, #(name, domain), codomain, _) -> {
      let domain_val = evaluate(ffi, env, domain)
      ast.VPi(implicit, #(name, domain_val), #(env, codomain))
    }
    ast.Fix(name, body, _) -> ast.VFix(name, #(env, body))
    ast.App(fun, arg, _) -> {
      let fun_val = evaluate(ffi, env, fun)
      let arg_val = evaluate(ffi, env, arg)
      do_app(ffi, fun_val, arg_val)
    }
    ast.Union(variants, _) -> {
      let variants_val = variants
      // ast.VTypeDef(variants_val)
      todo
    }
    ast.Match(arg, cases, _) -> {
      todo
    }
    ast.Err(_) -> ast.VErr
  }
}

fn do_app(ffi: FFI, fun: ast.Value, arg: ast.Value) -> ast.Value {
  case fun {
    // Neutral application
    ast.VNeut(neut_fun) -> ast.vapp(neut_fun, arg)
    // Explicit parameter: β-reduction
    ast.VLam(False, _, #(env, body)) -> evaluate(ffi, [arg, ..env], body)
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
