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
  unwrap_seen(ffi, subst, value, [])
}

/// Like `unwrap`, but carrying a stack of hole IDs currently being
/// resolved so self-referential solutions terminate.
pub fn unwrap_seen(
  ffi: FFI,
  subst: Subst,
  value: Value,
  seen: List(Int),
) -> Value {
  case value {
    v.Neut(neut) -> unwrap_neut(ffi, subst, neut, seen)
    _ -> value
  }
}

/// eval → unwrap → quote: fully resolve a term to a hole-free Term.
pub fn unwrap_term(ffi: FFI, subst: Subst, env: Env, term: Term) -> Term {
  eval(ffi, env, term)
  |> unwrap(ffi, subst, _)
  |> quote(ffi, list.length(env), _)
}

pub fn unwrap_neut(
  ffi: FFI,
  subst: Subst,
  neut: Neut,
  seen: List(Int),
) -> Value {
  case neut {
    v.NVar(level) -> v.var(level)
    v.NHole(env, None) -> v.hole_open(env, None)
    v.NHole(env, Some(id)) ->
      case list.contains(seen, id) {
        True -> v.hole(env, id)
        False ->
          case list.key_find(subst, id) {
            // The solution was computed in (possibly) a different
            // environment, so quote it against *this* hole's captured
            // env before re-evaluating: that turns the solution's
            // variable levels into indices valid here.
            Ok(solution) ->
              unwrap_seen(ffi, subst, solution, [id, ..seen])
              |> quote.normalize_value(ffi, env, _)
            Error(Nil) -> v.hole(env, id)
          }
      }
    // Once the head unwraps to a concrete lambda/fix, the whole
    // application can reduce and the neutral is eliminated.
    v.NApp(fun_neut, arg) -> {
      case unwrap_neut(ffi, subst, fun_neut, seen) {
        v.Neut(fun_neut) -> v.app(fun_neut, arg)
        fun ->
          eval.do_app(ffi, fun, arg)
          |> unwrap_seen(ffi, subst, _, seen)
      }
    }
    v.NMatch(env, arg_neut, cases) -> {
      case unwrap_neut(ffi, subst, arg_neut, seen) {
        v.Neut(arg_neut) -> v.match(env, arg_neut, cases)
        arg ->
          eval.do_match(ffi, env, arg, cases)
          |> unwrap_seen(ffi, subst, _, seen)
      }
    }
    v.NCall(name, ret, arg) -> {
      let arg = unwrap_seen(ffi, subst, arg, seen)
      eval.do_call(ffi, name, ret, arg)
    }
  }
}
