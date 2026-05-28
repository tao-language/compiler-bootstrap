import core/ast
import core/state.{type FFI}
import core/utils
import gleam/list
import gleam/option.{type Option, None, Some}

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
  case arg {
    ast.VNeut(arg_neut) -> ast.vmatch(env, arg_neut, cases)
    _ -> do_match_case_list(ffi, env, arg, cases)
  }
}

fn do_match_case_list(
  ffi: FFI,
  env: ast.Env,
  arg: ast.Value,
  cases: List(ast.Case),
) -> ast.Value {
  case cases {
    [] -> ast.VErr
    [case_, ..cases] ->
      case do_match_case(ffi, env, arg, case_) {
        Some(env) -> eval(ffi, env, case_.body)
        None -> do_match_case_list(ffi, env, arg, cases)
      }
  }
}

fn do_match_case(
  ffi: FFI,
  env: ast.Env,
  arg: ast.Value,
  case_: ast.Case,
) -> Option(ast.Env) {
  case match_pattern(case_.pattern, arg) {
    Some(bindings) -> {
      let env = list.append(bindings, env)
      case case_.guard {
        Some(guard) -> do_match_guard(ffi, env, guard)
        None -> Some(env)
      }
    }
    None -> None
  }
}

fn do_match_guard(
  ffi: FFI,
  env: ast.Env,
  guard: #(ast.Term, ast.Pattern),
) -> Option(ast.Env) {
  let #(guard_term, guard_pattern) = guard
  let guard_value = eval(ffi, env, guard_term)
  case match_pattern(guard_pattern, guard_value) {
    Some(bindings) -> Some(list.append(bindings, env))
    None -> None
  }
}

pub fn match_pattern(
  pattern: ast.Pattern,
  value: ast.Value,
) -> Option(List(ast.Value)) {
  case pattern, value {
    ast.PAny(_), _ -> Some([])
    ast.PTyp(u1, _), ast.VTyp(u2) if u1 == u2 -> Some([])
    ast.PLit(k1, _), ast.VLit(k2) if k1 == k2 -> Some([])
    ast.PLitT(k1, _), ast.VLitT(k2) if k1 == k2 -> Some([])
    ast.PAlias(_, pattern, _), _ ->
      case match_pattern(pattern, value) {
        Some(bindings) -> Some([value, ..bindings])
        None -> None
      }
    ast.PCtr(tag1, pattern, _), ast.VCtr(tag2, arg) if tag1 == tag2 ->
      match_pattern(pattern, arg)
    ast.PRcd(pfields, _), ast.VRcd(vfields) ->
      match_pattern_rcd(pfields, vfields)
    ast.PError(_), ast.VErr -> Some([])
    _, _ -> None
  }
}

fn match_pattern_rcd(
  pfields: List(#(String, ast.Pattern)),
  vfields: List(#(String, ast.Value)),
) -> Option(List(ast.Value)) {
  case pfields {
    [] -> Some([])
    [#(pname, p), ..rest] -> {
      case list.find(vfields, fn(field) {
        let #(vname, _) = field
        vname == pname
      }) {
        Error(_) -> None
        Ok(#(_, v)) ->
          case match_pattern(p, v) {
            Some(bindings) ->
              case match_pattern_rcd(rest, vfields) {
                Some(rest_bindings) -> Some(list.append(bindings, rest_bindings))
                None -> None
              }
            None -> None
          }
      }
    }
  }
}
