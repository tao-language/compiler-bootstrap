import core/context.{type Subst}
import core/eval
import core/ffi.{type FFI}
import core/quote
import core/step.{step}
import core/trace
import core/value.{type Neut, type Value} as v
import gleam/int
import gleam/list
import gleam/option.{None, Some}

/// Looks up a hole in the substitution table,
/// recursively stripping away solved wrappers.
pub fn unwrap(ffi: FFI, subst: Subst, value: Value) -> Value {
  step("unwrap:unwrap")
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
  step("unwrap:unwrap_seen")
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
  step("unwrap:unwrap_neut")
  case neut {
    v.NVar(level) -> v.var(level)
    v.NHole(env, None) -> v.hole_open(env, None)
    v.NHole(env, Some(id)) ->
      case list.contains(seen, id) {
        True -> v.hole(env, id)
        False ->
          case list.key_find(subst, id) {
            // The solution's variable levels address the frame the
            // solution was produced in (the stored solve env), which
            // may contain bindings (pattern variables, quantifier
            // parameters) absent from the hole's shorter captured env.
            Ok(#(solve_env, solution)) -> {
              trace.anchor(id, env, solve_env)
              unwrap_seen(ffi, subst, solution, [id, ..seen])
              |> quote.normalize_value(ffi, solve_env, _)
            }
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

/// The largest `NVar` level occurring in a value (quantifier bodies are
/// terms and carry indices, not levels). `-1` when the value is closed.
pub fn max_neut_level(value: Value, max: Int) -> Int {
  step("unwrap:max_neut_level")
  case value {
    v.Neut(v.NVar(level)) -> int.max(max, level)
    v.Neut(v.NApp(fun, arg)) ->
      int.max(max_neut_level(v.Neut(fun), max), max_neut_level(arg, max))
    v.Neut(v.NMatch(_, arg, _cases)) -> max_neut_level(arg, max)
    v.Neut(v.NCall(_, ret, arg)) ->
      int.max(max_neut_level(ret, max), max_neut_level(arg, max))
    v.Neut(_other) -> max
    v.Ctr(_tag, arg) -> max_neut_level(arg, max)
    v.Rcd(fields, tail) -> {
      let m =
        list.fold(fields, max, fn(acc, field) {
          let #(_, #(val, default)) = field
          let acc = max_neut_level(val, acc)
          case default {
            Some(d) -> max_neut_level(d, acc)
            None -> acc
          }
        })
      case tail {
        Some(t) -> max_neut_level(t, m)
        None -> m
      }
    }
    v.For(_, #(_, param), _body) -> max_neut_level(param, max)
    v.Lam(_, #(_, param), _body) -> max_neut_level(param, max)
    v.Pi(_, #(_, param), _body) -> max_neut_level(param, max)
    v.TypeDef(_, v.TypeDefinition(params, _arg, variants)) -> {
      let m =
        list.fold(params, max, fn(acc, param) {
          let #(_, typ) = param
          max_neut_level(typ, acc)
        })
      list.fold(variants, m, fn(acc, variant) {
        let #(_, v.Variant(vparams, _varg, _vret)) = variant
        list.fold(vparams, acc, fn(acc2, param) {
          let #(_, typ) = param
          max_neut_level(typ, acc2)
        })
      })
    }
    _ -> max
  }
}
