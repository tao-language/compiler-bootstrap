import core/ffi.{type FFI}
import core/term.{type Case, type Pattern, type Term} as tm
import core/value.{type Env, type Type, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import utils/list_utils.{list_at}

pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  case term {
    tm.Typ(universe) -> v.Typ(universe)
    tm.Hole(id) -> v.hole(id)
    tm.Lit(value) -> v.Lit(value)
    tm.LitT(value) -> v.LitT(value)
    tm.Var(index) ->
      case list_at(env, index) {
        Some(value) -> value
        None -> v.Err
      }
    tm.Ctr(tag, arg) -> v.Ctr(tag, eval(ffi, env, arg))
    tm.Rcd(fields, tail) -> {
      let fields_val =
        list.map(fields, fn(field) {
          let #(name, #(term, default)) = field
          let value = eval(ffi, env, term)
          let default_val = option.map(default, eval(ffi, env, _))
          #(name, #(value, default_val))
        })
      let tail_val = option.map(tail, eval(ffi, env, _))
      v.Rcd(fields_val, tail_val)
    }
    tm.Call(name, returns, args) -> {
      let returns_val = eval(ffi, env, returns)
      let args_val = list.map(args, eval(ffi, env, _))
      do_call(ffi, name, returns_val, args_val)
    }
    tm.Ann(term, _) -> eval(ffi, env, term)
    tm.Lam(_, #(name, param), body) -> {
      let param_val = eval(ffi, env, param)
      v.Lam(env, #(name, param_val), body)
    }
    tm.Pi(implicit, #(name, domain), codomain) -> {
      let domain_val = eval(ffi, env, domain)
      v.Pi(env, implicit, #(name, domain_val), codomain)
    }
    tm.Fix(name, body) -> v.Fix(env, name, body)
    tm.App(_, fun, arg) -> {
      let fun_val = eval(ffi, env, fun)
      let arg_val = eval(ffi, env, arg)
      do_app(ffi, fun_val, arg_val)
    }
    tm.TypeDef(tm.TypeDefinition(params, arg, variants)) -> {
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

pub fn do_app(ffi: FFI, fun_val: Value, arg_val: Value) -> Value {
  case fun_val {
    // Neutral application
    v.Neut(neut_fun) -> v.app(neut_fun, arg_val)
    // Lambda application: β-reduction
    v.Lam(env, _, body) -> eval(ffi, [arg_val, ..env], body)
    // Recursive function application
    v.Fix(env, _, body) -> {
      let body_val = eval(ffi, [fun_val, ..env], body)
      do_app(ffi, body_val, arg_val)
    }
    // Not a function
    _ -> v.Err
  }
}

pub fn do_call(
  ffi: FFI,
  name: String,
  returns: Type,
  args_val: List(Value),
) -> Value {
  let result = case list.key_find(ffi, name) {
    Ok(call) -> call(args_val)
    Error(Nil) -> None
  }
  case result {
    Some(value) -> value
    None -> v.call(name, returns, args_val)
  }
}

pub fn do_match(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  cases: List(Case),
) -> Value {
  case arg_val {
    v.Neut(arg_neut) -> v.match(env, arg_neut, cases)
    _ -> do_match_case_list(ffi, env, arg_val, cases)
  }
}

fn do_match_case_list(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  cases: List(Case),
) -> Value {
  case cases {
    [] -> v.Err
    [case_, ..cases] ->
      case do_match_case(ffi, env, arg_val, case_) {
        Some(env) -> eval(ffi, env, case_.body)
        None -> do_match_case_list(ffi, env, arg_val, cases)
      }
  }
}

fn do_match_case(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  case_: Case,
) -> Option(Env) {
  case match_pattern(case_.pattern, arg_val) {
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
    tm.PRcd([], None), v.Rcd([], None) -> Some([])
    tm.PRcd([], Some(ptail)), value -> match_pattern(ptail, value)
    tm.PRcd([#(name, pat), ..pfields], ptail), value ->
      match_pattern_rcd_field(name, pat, value)
      |> option.then(fn(xs_value) {
        let #(xs, value) = xs_value
        case match_pattern(tm.PRcd(pfields, ptail), value) {
          Some(ys) -> Some(list.append(ys, xs))
          None -> None
        }
      })
    tm.PErr, v.Err -> Some([])
    _, _ -> None
  }
}

fn match_pattern_rcd_field(
  name: String,
  pattern: Pattern,
  value: Value,
) -> Option(#(List(Value), Value)) {
  case value {
    v.Rcd(vfields, opt_vtail) ->
      case list.key_pop(vfields, name) {
        Ok(#(#(value, _default), vfields)) ->
          match_pattern(pattern, value)
          |> option.map(fn(xs) { #(xs, v.Rcd(vfields, opt_vtail)) })
        Error(Nil) ->
          opt_vtail
          |> option.then(match_pattern_rcd_field(name, pattern, _))
          |> option.map(fn(xs_vtail) {
            let #(xs, vtail) = xs_vtail
            #(xs, v.Rcd(vfields, Some(vtail)))
          })
      }
    _ -> None
  }
}
