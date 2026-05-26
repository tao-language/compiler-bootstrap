import core/ast
import core/state.{type FFI}
import core/utils
import gleam/list
import gleam/option.{None, Some}

/// Evaluate a Value's De Bruijn references in an environment.
/// This resolves any HVar references to their actual values in the env.
pub fn eval_value(ffi: FFI, env: ast.Env, value: ast.Value) -> ast.Value {
  case value {
    ast.VTyp(u) -> ast.VTyp(u)
    ast.VLit(lit) -> ast.VLit(lit)
    ast.VLitT(lit) -> ast.VLitT(lit)
    ast.VCtr(tag, arg) -> ast.VCtr(tag, eval_value(ffi, env, arg))
    ast.VRcd(fields) ->
      ast.VRcd(
        list.map(fields, fn(field) {
          let #(name, val) = field
          #(name, eval_value(ffi, env, val))
        }),
      )
    ast.VRcdT(fields) ->
      ast.VRcdT(
        list.map(fields, fn(field) {
          let #(name, val, default) = field
          #(
            name,
            eval_value(ffi, env, val),
            option.map(default, eval_value(ffi, env, _)),
          )
        }),
      )
    ast.VNeut(head, spine) ->
      case head {
        ast.HVar(level) ->
          case utils.list_at(env, level) {
            Some(resolved_val) -> resolved_val
            None -> ast.VNeut(ast.HVar(level), spine)
          }
        ast.HHole(id) -> ast.vhole(id, spine)
        ast.HCall(name, args) -> {
          let resolved_args = list.map(args, eval_value(ffi, env, _))
          ast.vcall(name, resolved_args, spine)
        }
      }
    ast.VLam(..) -> value
    // Skip lambda env evaluation for now
    ast.VPi(implicits, domain, codomain) -> {
      let resolved_implicits =
        list.map(implicits, fn(imp) {
          let #(name, val) = imp
          #(name, eval_value(ffi, env, val))
        })
      let domain_val = eval_value(ffi, env, domain.1)
      let codomain_val = eval_value(ffi, env, codomain)
      ast.VPi(resolved_implicits, #(domain.0, domain_val), codomain_val)
    }
    ast.VTypeDef(params, constructors) ->
      ast.VTypeDef(
        list.map(params, fn(p) {
          let #(name, val) = p
          #(name, eval_value(ffi, env, val))
        }),
        constructors,
      )
    ast.VErr -> ast.VErr
  }
}

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
      let result = case list.key_find(ffi, name) {
        Ok(call) -> call(args_val)
        Error(Nil) -> None
      }
      case result {
        Some(value) -> value
        None -> ast.vcall(name, args_val, [])
      }
    }
    ast.Ann(term, _, _) -> eval(ffi, env, term)
    ast.Lam(implicits, #(name, param), body, _) -> {
      let implicits_val = eval_params(ffi, env, implicits)
      let param_val = eval(ffi, env, param)
      ast.VLam(env, implicits_val, #(name, param_val), body)
    }
    ast.Pi(implicits, #(name, domain), codomain, _) -> {
      todo
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

fn eval_params(
  ffi: FFI,
  env: ast.Env,
  params: List(#(String, ast.Term)),
) -> List(#(String, ast.Value)) {
  list.map(params, fn(param) {
    let #(name, term) = param
    #(name, eval(ffi, env, term))
  })
}
