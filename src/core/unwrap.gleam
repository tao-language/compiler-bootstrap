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
    v.NHole(env, None) -> v.hole(env, None)
    v.NHole(env, Some(id)) ->
      case list.key_find(subst, id) {
        Ok(solution) ->
          unwrap(ffi, subst, solution)
          |> quote.normalize_value(ffi, env, _)
        Error(Nil) -> v.hole(env, Some(id))
      }
    v.NApp(fun_neut, arg) -> {
      case unwrap_neut(ffi, subst, fun_neut) {
        v.Neut(fun_neut) -> v.app(fun_neut, arg)
        fun ->
          eval.do_app(ffi, fun, arg)
          |> unwrap(ffi, subst, _)
      }
    }
    v.NMatch(env, arg_neut, cases) -> {
      case unwrap_neut(ffi, subst, arg_neut) {
        v.Neut(arg_neut) -> v.match(env, arg_neut, cases)
        arg ->
          eval.do_match(ffi, env, arg, cases)
          |> unwrap(ffi, subst, _)
      }
    }
    v.NCall(name, returns, args) -> {
      // TODO: should have single arg
      let returns = unwrap(ffi, subst, returns)
      let args = list.map(args, unwrap(ffi, subst, _))
      eval.do_call(ffi, name, returns, args)
    }
  }
}
