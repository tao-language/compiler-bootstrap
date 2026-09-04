/// Quote — Convert Values back to Terms
import core/ast
import core/eval.{eval}
import core/ffi.{type FFI}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

/// eval → quote: reduce a term and turn it back into a term whose
/// variables are de Bruijn indices into `env`.
pub fn normalize_term(ffi: FFI, env: Env, term: Term) -> Term {
  eval(ffi, env, term)
  |> quote(ffi, env, _)
}

/// quote → eval: re-express a value's holes as terms relative to `env`,
/// then re-evaluate. Used to transplant a hole solution captured in a
/// different environment into the current one.
pub fn normalize_value(ffi: FFI, env: Env, value: Value) -> Value {
  quote(ffi, env, value)
  |> eval(ffi, env, _)
}

/// quote → lift: a value as a named AST expression (for display).
pub fn lift(
  ffi: FFI,
  env: Env,
  names: List(String),
  value: Value,
  span: Span,
) -> ast.Expr {
  quote(ffi, env, value)
  |> tm.lift(names, span)
}

/// Turn a Value back into a Term. `env` is the environment the value's
/// neutral variables are relative to, so a neutral `NVar(level)` becomes
/// `Var(len(env) - level - 1)` — the de Bruijn index of that level in `env`.
/// Bodies of `For`/`Lam`/`Pi`/`Fix` are re-normalized in their own 
/// captured environments plus one fresh parameter slot.
pub fn quote(ffi: FFI, env: Env, value: Value) -> Term {
  case value {
    v.Typ(universe) -> tm.Typ(universe)
    v.Lit(lit) -> tm.Lit(lit)
    v.LitT(lit) -> tm.LitT(lit)
    v.Ctr(tag, arg_val) -> tm.Ctr(tag, quote(ffi, env, arg_val))
    v.Rcd(fields_val, tail_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, #(value, default_val)) = field
          let term = quote(ffi, env, value)
          let default = option.map(default_val, quote(ffi, env, _))
          #(name, #(term, default))
        })
      let tail = option.map(tail_val, quote(ffi, env, _))
      tm.Rcd(fields, tail)
    }
    v.Neut(neut) -> quote_neut(ffi, env, neut)
    v.For(captured, #(name, param_val), body) -> {
      let param = quote(ffi, captured, param_val)
      let body = normalize_term(ffi, v.env_push(captured, 1), body)
      tm.For(#(name, param), body)
    }
    v.Lam(captured, #(name, param_val), body) -> {
      let param = quote(ffi, captured, param_val)
      let body = normalize_term(ffi, v.env_push(captured, 1), body)
      tm.Lam(#(name, param), body)
    }
    v.Pi(captured, #(name, param_val), body) -> {
      let param = quote(ffi, captured, param_val)
      let body = normalize_term(ffi, v.env_push(captured, 1), body)
      tm.Pi(#(name, param), body)
    }
    v.Fix(captured, name, body) -> {
      let body = normalize_term(ffi, v.env_push(captured, 1), body)
      tm.Fix(name, body)
    }
    v.TypeDef(_, _) -> todo
    v.Err -> tm.Err
  }
}

fn quote_neut(ffi: FFI, env: Env, neut: Neut) -> Term {
  case neut {
    // Level → de Bruijn index: index = env_size - level - 1 (see `Value`).
    v.NVar(level) -> tm.Var(list.length(env) - level - 1)
    // A hole quotes as itself; only exact structural equality with a
    // placeholder of the same size would ever match, so this is a stable
    // `tm.Hole(id)` (re-resolved later by `resolve`).
    v.NHole(_captured, id) -> tm.Hole(id)
    v.NApp(fun_neut, arg_val) -> {
      let fun = quote_neut(ffi, env, fun_neut)
      let arg = quote(ffi, env, arg_val)
      tm.App(fun, arg)
    }
    v.NMatch(captured_env, arg_neut, cases) -> {
      let arg = quote_neut(ffi, captured_env, arg_neut)
      let cases = list.map(cases, quote_case(ffi, captured_env, _))
      tm.Match(arg, cases)
    }
    v.NCall(name, ret_val, arg_val) -> {
      let ret = quote(ffi, env, ret_val)
      let arg = quote(ffi, env, arg_val)
      tm.Call(name, ret, arg)
    }
  }
}

fn quote_case(ffi: FFI, env: Env, c: Case) -> Case {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  let #(guard, env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let env = v.env_push(env, list.length(tm.bindings(g_pattern)))
      let g_term = normalize_term(ffi, env, g_term)
      #(Some(#(g_term, g_pattern)), env)
    }
    None -> #(None, env)
  }
  let body = normalize_term(ffi, env, c.body)
  tm.Case(c.pattern, guard, body)
}
