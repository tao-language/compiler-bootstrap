import core/context.{type Subst}
import core/eval.{eval}
import core/ffi.{type FFI}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

/// Looks up a hole in the substitution table,
/// recursively stripping away solved wrappers.
pub fn unwrap(ffi: FFI, subst: Subst, value: Value) -> Value {
  case value {
    v.Neut(neut) -> unwrap_neut(ffi, subst, neut)
    _ -> value
  }
}

pub fn unwrap_term(ffi: FFI, subst: Subst, env: Env, term: Term) -> Term {
  eval(ffi, env, term)
  |> unwrap(ffi, subst, _)
  |> quote(ffi, list.length(env), _)
}

pub fn unwrap_neut(ffi: FFI, subst: Subst, neut: Neut) -> Value {
  case neut {
    v.NVar(level) -> v.var(level)
    v.NHole(id) ->
      case list.key_find(subst, id) {
        Ok(solution) -> unwrap(ffi, subst, solution)
        Error(Nil) -> v.hole(id)
      }
    v.NApp(fun_neut, arg) -> {
      let fun = unwrap_neut(ffi, subst, fun_neut)
      eval.do_app(ffi, fun, arg)
    }
    v.NMatch(env, arg_neut, cases) -> {
      let arg = unwrap_neut(ffi, subst, arg_neut)
      let cases = list.map(cases, unwrap_case(ffi, subst, env, _))
      eval.do_match(ffi, env, arg, cases)
    }
    v.NCall(name, returns, args) -> {
      let returns = unwrap(ffi, subst, returns)
      let args = list.map(args, unwrap(ffi, subst, _))
      eval.do_call(ffi, name, returns, args)
    }
  }
}

fn unwrap_case(ffi: FFI, subst: Subst, env: Env, c: Case) -> Case {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  let #(guard, env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let env = v.env_push(env, list.length(tm.bindings(g_pattern)))
      let g_term = unwrap_term(ffi, subst, env, g_term)
      #(Some(#(g_term, g_pattern)), env)
    }
    None -> #(None, env)
  }
  tm.Case(c.pattern, guard, unwrap_term(ffi, subst, env, c.body))
}
