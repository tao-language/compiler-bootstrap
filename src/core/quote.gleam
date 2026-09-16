/// Quote — Convert Values back to Terms
import core/eval.{eval}
import core/ffi.{type FFI}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

/// eval → quote: reduce a term and turn it back into a term whose
/// variables are de Bruijn indices into `env`.
pub fn normalize_term(ffi: FFI, env: Env, term: Term) -> Term {
  normalize_term_rec(ffi, env, term, 0)
}

fn normalize_term_rec(ffi: FFI, env: Env, term: Term, depth: Int) -> Term {
  eval(ffi, env, term)
  |> quote_rec(ffi, env, _, depth)
}

/// quote → eval: re-express a value's holes as terms relative to `env`,
/// then re-evaluate. Used to transplant a hole solution captured in a
/// different environment into the current one.
pub fn normalize_value(ffi: FFI, env: Env, value: Value) -> Value {
  quote(ffi, env, value)
  |> eval(ffi, env, _)
}

/// Turn a Value back into a Term. `env` is the environment the value's
/// neutral variables are relative to, so a neutral `NVar(level)` becomes
/// `Var(len(env) - level - 1)` — the de Bruijn index of that level in `env`.
/// Bodies of `For`/`Lam`/`Pi`/`Fix` are re-normalized in their own 
/// captured environments plus one fresh parameter slot.
pub fn quote(ffi: FFI, env: Env, value: Value) -> Term {
  quote_rec(ffi, env, value, 0)
}

// Bounds the eval↔quote cycle that never terminates on self-referential
// types (see docs/implicit-args.md, Limitations).
const max_depth = 10000

const depth_exceeded =
  "error: the compiler hit a deeply recursive type while simplifying (recursive implicit function types are not supported yet; see docs/implicit-args.md)"

fn quote_rec(ffi: FFI, env: Env, value: Value, depth: Int) -> Term {
  case depth > max_depth {
    True -> panic as depth_exceeded
    False -> quote_step(ffi, env, value, depth)
  }
}

fn quote_step(ffi: FFI, env: Env, value: Value, depth: Int) -> Term {
  case value {
    v.Typ(universe) -> tm.Typ(universe)
    v.Lit(lit) -> tm.Lit(lit)
    v.LitT(lit) -> tm.LitT(lit)
    v.Ctr(tag, arg_val) -> tm.Ctr(tag, quote_rec(ffi, env, arg_val, depth + 1))
    v.Rcd(fields_val, tail_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, #(value, default_val)) = field
          let term = quote_rec(ffi, env, value, depth + 1)
          let default = option.map(default_val, fn(d) { quote_rec(ffi, env, d, depth + 1) })
          #(name, #(term, default))
        })
      let tail = option.map(tail_val, fn(t) { quote_rec(ffi, env, t, depth + 1) })
      tm.Rcd(fields, tail)
    }
    v.Neut(neut) -> quote_neut_rec(ffi, env, neut, depth)
    v.For(captured, #(name, param_val), body) -> {
      let param = quote_rec(ffi, captured, param_val, depth + 1)
      let body = normalize_term_rec(ffi, v.env_push(captured, 1), body, depth + 1)
      tm.For(#(name, param), body)
    }
    v.Lam(captured, #(name, param_val), body) -> {
      let param = quote_rec(ffi, captured, param_val, depth + 1)
      let body = normalize_term_rec(ffi, v.env_push(captured, 1), body, depth + 1)
      tm.Lam(#(name, param), body)
    }
    v.Pi(captured, #(name, param_val), body) -> {
      let param = quote_rec(ffi, captured, param_val, depth + 1)
      let body = normalize_term_rec(ffi, v.env_push(captured, 1), body, depth + 1)
      tm.Pi(#(name, param), body)
    }
    v.Fix(captured, name, body) -> {
      let body = normalize_term_rec(ffi, v.env_push(captured, 1), body, depth + 1)
      tm.Fix(name, body)
    }
    // Type definitions: quote the parameter types in the captured
    // frame; the argument and variant terms in frames where the
    // parameters (and, for variants, the variant's own parameters) are
    // bound, like `For`/`Pi` bodies.
    v.TypeDef(captured, v.TypeDefinition(params, arg, variants)) -> {
      let p_env = v.env_push(captured, list.length(params))
      let params =
        list.map(params, fn(param) {
          let #(name, typ) = param
          #(name, quote_rec(ffi, captured, typ, depth + 1))
        })
      let arg = normalize_term_rec(ffi, p_env, arg, depth + 1)
      let variants =
        list.map(variants, fn(variant) {
          let #(tag, v.Variant(vparams, varg, vret)) = variant
          let vp_env = v.env_push(p_env, list.length(vparams))
          let vparams =
            list.map(vparams, fn(param) {
              let #(name, typ) = param
              #(name, quote_rec(ffi, p_env, typ, depth + 1))
            })
          #(
            tag,
            tm.Variant(
              vparams,
              normalize_term_rec(ffi, vp_env, varg, depth + 1),
              normalize_term_rec(ffi, vp_env, vret, depth + 1),
            ),
          )
        })
      tm.TypeDef(tm.TypeDefinition(params, arg, variants))
    }
    v.Err -> tm.Err
  }
}

fn quote_neut_rec(ffi: FFI, env: Env, neut: Neut, depth: Int) -> Term {
  case neut {
    // Level → de Bruijn index: index = env_size - level - 1 (see `Value`).
    v.NVar(level) -> tm.Var(list.length(env) - level - 1)
    // A hole quotes as itself; only exact structural equality with a
    // placeholder of the same size would ever match, so this is a stable
    // `tm.Hole(id)` (re-resolved later by `resolve`).
    v.NHole(_captured, id) -> tm.Hole(id)
    v.NApp(fun_neut, arg_val) -> {
      let fun = quote_neut_rec(ffi, env, fun_neut, depth + 1)
      let arg = quote_rec(ffi, env, arg_val, depth + 1)
      tm.App(fun, arg)
    }
    v.NMatch(captured_env, arg, cases) -> {
      // Body terms are indexed into `captured_env`; the values' neutral
      // levels are only addressable in `env`, the placement frame.
      // `quote_case` keeps both conventions valid at once.
      let arg = quote_rec(ffi, env, arg, depth + 1)
      let cases =
        list.map(cases, fn(c) { quote_case(ffi, env, captured_env, c, depth + 1) })
      tm.Match(arg, cases)
    }
    v.NCall(name, ret_val, arg_val) -> {
      let ret = quote_rec(ffi, env, ret_val, depth + 1)
      let arg = quote_rec(ffi, env, arg_val, depth + 1)
      tm.Call(name, ret, arg)
    }
  }
}

/// Quote one match case.
///
/// The body's de Bruijn *indices* index into `captured_env` (the env the
/// match got stuck in), but the values' neutral *levels* are only
/// addressable in `env` (the env the match is placed in). So eval and
/// quote use different frames:
/// - `eval_env`  = `[placeholders, ..captured_env]`, so the body's
///   `Var(k)` lookups bind to the same values as when the body was written;
/// - `quote_env` = `env_push(env, n)`, so level→index translation lands in
///   the placement frame.
///
/// Each placeholder carries the level it would have in `env_push(env, n)`,
/// so it re-quotes to the pattern binding's own `Var(i)`; when
/// `captured_env == env` the two frames coincide and this reduces to a
/// plain `normalize_term`.
fn quote_case(ffi: FFI, env: Env, captured_env: Env, c: Case, depth: Int) -> Case {
  let num_bindings = list.length(tm.bindings(c.pattern))
  let eval_env = placeholder_env(env, num_bindings, captured_env)
  let quote_env = v.env_push(env, num_bindings)
  let #(guard, eval_env, quote_env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let num_guard = list.length(tm.bindings(g_pattern))
      let eval_env = placeholder_env(quote_env, num_guard, eval_env)
      let quote_env = v.env_push(quote_env, num_guard)
      let g_term =
        eval(ffi, eval_env, g_term) |> quote_rec(ffi, quote_env, _, depth + 1)
      #(Some(#(g_term, g_pattern)), eval_env, quote_env)
    }
    None -> #(None, eval_env, quote_env)
  }
  let body = eval(ffi, eval_env, c.body) |> quote_rec(ffi, quote_env, _, depth + 1)
  tm.Case(c.pattern, guard, body)
}

/// `env_push(levels_env, num)` with `frame` substituted for `levels_env`:
/// the same `num` placeholder bindings (innermost first) layered over the
/// term frame, so a body's `Var(0..num-1)` fetches them and they re-quote
/// to themselves in `env_push(levels_env, num)`.
fn placeholder_env(levels_env: Env, num: Int, frame: Env) -> Env {
  list.append(list.take(v.env_push(levels_env, num), num), frame)
}
