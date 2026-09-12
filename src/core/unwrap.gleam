import core/context.{type Subst}
import core/eval
import core/ffi.{type FFI}
import core/quote
import core/value.{type Neut, type Value} as v
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
            Ok(#(_, solution)) ->
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
    // Re-reduce the match with the re-unwrapped scrutinee: cases that
    // were undecided may now be decided (the same three-valued
    // criterion as `do_match` itself, so there is no eager/defer
    // asymmetry). If it is still stuck, keep the neutral match with the
    // re-unwrapped arg *without* re-unwrapping it: `do_match` produced
    // it from the already-unwrapped arg, so unwrapping it again would
    // just re-run the same match forever.
    v.NMatch(env, arg, cases) -> {
      let arg = unwrap_seen(ffi, subst, arg, seen)
      case eval.do_match(ffi, env, arg, cases) {
        v.Neut(v.NMatch(_, _, _)) -> v.match(env, arg, cases)
        value -> unwrap_seen(ffi, subst, value, seen)
      }
    }
    v.NCall(name, ret, arg) -> {
      let arg = unwrap_seen(ffi, subst, arg, seen)
      eval.do_call(ffi, name, ret, arg)
    }
  }
}
