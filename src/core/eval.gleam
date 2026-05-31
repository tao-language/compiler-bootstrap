import core/context.{type FFI}
import core/term.{type Case, type Pattern, type Term} as tm
import core/utils
import core/value.{type Env, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}

pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  case term {
    tm.Typ(universe) -> v.Typ(universe)
    tm.Hole(id) -> v.hole(id)
    tm.Lit(value) -> v.Lit(value)
    tm.LitT(value) -> v.LitT(value)
    tm.Var(index) ->
      case utils.list_at(env, index) {
        Some(value) -> value
        None -> v.Err
      }
    tm.Ctr(tag, arg) -> v.Ctr(tag, eval(ffi, env, arg))
    tm.Rcd(fields) ->
      v.Rcd(
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, eval(ffi, env, term))
        }),
      )
    tm.RcdT(fields) ->
      v.RcdT(
        list.map(fields, fn(field) {
          let #(name, #(term, maybe_default)) = field
          let value = eval(ffi, env, term)
          let default = option.map(maybe_default, eval(ffi, env, _))
          #(name, #(value, default))
        }),
      )
    tm.Call(name, args) -> {
      let args_val = list.map(args, eval(ffi, env, _))
      let result = case list.key_find(ffi, name) {
        Ok(call) -> call(args_val)
        Error(Nil) -> None
      }
      case result {
        Some(value) -> value
        None -> v.call(name, args_val)
      }
    }
    tm.Ann(term, _) -> eval(ffi, env, term)
    tm.Lam(implicit, #(name, param), body) -> {
      let param_val = eval(ffi, env, param)
      v.Lam(env, implicit, #(name, param_val), body)
    }
    tm.Pi(implicit, #(name, domain), codomain) -> {
      let domain_val = eval(ffi, env, domain)
      v.Pi(env, implicit, #(name, domain_val), codomain)
    }
    tm.Fix(name, body) -> v.Fix(name, #(env, body))
    tm.App(fun, arg) -> {
      let fun_val = eval(ffi, env, fun)
      let arg_val = eval(ffi, env, arg)
      do_app(ffi, fun_val, arg_val)
    }
    tm.TypeDef(params, variants) -> {
      echo term
      todo
    }
    tm.Match(arg, cases) -> {
      let arg_val = eval(ffi, env, arg)
      do_match(ffi, env, arg_val, cases)
    }
    tm.Err -> v.Err
  }
}

fn do_app(ffi: FFI, fun: Value, arg: Value) -> Value {
  case fun {
    // Neutral application
    v.Neut(neut_fun) -> v.app(neut_fun, arg)
    // Explicit parameter: β-reduction
    v.Lam(env, False, _, body) -> eval(ffi, [arg, ..env], body)
    // Implicit parameter: implicit expansion
    v.Lam(env, True, param, body) -> {
      // Implicit parameters are expanded and solved during elaboration.
      todo as "Remove implicit from term.Lam and value.Lam"
    }
    _ -> v.Err
  }
}

fn do_match(ffi: FFI, env: Env, arg: Value, cases: List(Case)) -> Value {
  case arg {
    v.Neut(arg_neut) -> v.match(env, arg_neut, cases)
    _ -> do_match_case_list(ffi, env, arg, cases)
  }
}

fn do_match_case_list(
  ffi: FFI,
  env: Env,
  arg: Value,
  cases: List(Case),
) -> Value {
  case cases {
    [] -> v.Err
    [case_, ..cases] ->
      case do_match_case(ffi, env, arg, case_) {
        Some(env) -> eval(ffi, env, case_.body)
        None -> do_match_case_list(ffi, env, arg, cases)
      }
  }
}

fn do_match_case(ffi: FFI, env: Env, arg: Value, case_: Case) -> Option(Env) {
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

fn do_match_guard(ffi: FFI, env: Env, guard: #(Term, Pattern)) -> Option(Env) {
  let #(guard_term, guard_pattern) = guard
  let guard_value = eval(ffi, env, guard_term)
  case match_pattern(guard_pattern, guard_value) {
    Some(bindings) -> Some(list.append(bindings, env))
    None -> None
  }
}

pub fn match_pattern(pattern: Pattern, value: Value) -> Option(List(Value)) {
  case pattern, value {
    tm.PAny, _ -> Some([])
    tm.PTyp(u1), v.Typ(u2) if u1 == u2 -> Some([])
    tm.PLit(k1), v.Lit(k2) if k1 == k2 -> Some([])
    tm.PLitT(k1), v.LitT(k2) if k1 == k2 -> Some([])
    tm.PAlias(_, pattern), _ ->
      case match_pattern(pattern, value) {
        Some(bindings) -> Some([value, ..bindings])
        None -> None
      }
    tm.PCtr(tag1, pattern), v.Ctr(tag2, arg) if tag1 == tag2 ->
      match_pattern(pattern, arg)
    tm.PRcd(pfields), v.Rcd(vfields) -> match_pattern_rcd(pfields, vfields)
    tm.PError, v.Err -> Some([])
    _, _ -> None
  }
}

fn match_pattern_rcd(
  pfields: List(#(String, Pattern)),
  vfields: List(#(String, Value)),
) -> Option(List(Value)) {
  case pfields {
    [] -> Some([])
    [#(pname, p), ..rest] -> {
      case list.key_find(vfields, pname) {
        Error(_) -> None
        Ok(v) ->
          case match_pattern(p, v), match_pattern_rcd(rest, vfields) {
            // Prepend to respect DeBruijn index ordering.
            // For example, in `{x: a, y: b, z: c}`
            //    a is #2, b is #1, c is #0
            // So they should bind like `[c, b, a]`
            Some(xs), Some(ys) -> Some(list.append(ys, xs))
            _, _ -> None
          }
      }
    }
  }
}
