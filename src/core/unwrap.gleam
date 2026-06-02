import core/context.{type FFI, type Subst}
import core/eval
import core/value.{type Neut, type Value} as v
import gleam/list

/// Looks up a hole in the substitution table,
/// recursively stripping away solved wrappers.
pub fn unwrap(ffi: FFI, subst: Subst, value: Value) -> Value {
  case value {
    v.Neut(neut) -> unwrap_neut(ffi, subst, neut)
    _ -> value
  }
}

fn unwrap_neut(ffi: FFI, subst: Subst, neut: Neut) -> Value {
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
      eval.do_match(ffi, env, arg, cases)
    }
    v.NCall(name, args) -> {
      let args = list.map(args, unwrap(ffi, subst, _))
      eval.do_call(ffi, name, args)
    }
  }
}
