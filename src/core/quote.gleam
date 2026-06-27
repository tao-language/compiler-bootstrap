/// Quote — Convert Values back to Terms
import core/eval.{eval}
import core/ffi.{type FFI}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn normalize(ffi: FFI, env: Env, term: Term) -> Term {
  let value = eval(ffi, env, term)
  quote(ffi, list.length(env), value)
}

pub fn quote(ffi: FFI, size: Int, value: Value) -> Term {
  case value {
    v.Typ(universe) -> tm.Typ(universe)
    v.Lit(lit) -> tm.Lit(lit)
    v.LitT(lit) -> tm.LitT(lit)
    v.Ctr(tag, arg_val) -> tm.Ctr(tag, quote(ffi, size, arg_val))
    v.Rcd(fields_val, tail_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, #(value, default_val)) = field
          let term = quote(ffi, size, value)
          let default = option.map(default_val, quote(ffi, size, _))
          #(name, #(term, default))
        })
      let tail = option.map(tail_val, quote(ffi, size, _))
      tm.Rcd(fields, tail)
    }
    v.Neut(neut) -> quote_neut(ffi, size, neut)
    v.Lam(env, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let body = normalize(ffi, v.env_push(env, 1), body)
      tm.Lam(False, #(name, param), body)
    }
    v.Pi(env, implicit, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let body = normalize(ffi, v.env_push(env, 1), body)
      tm.Pi(implicit, #(name, param), body)
    }
    v.Fix(env, name, body) -> {
      let body = normalize(ffi, v.env_push(env, 1), body)
      tm.Fix(name, body)
    }
    v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> {
      todo
    }
    v.Err -> tm.Err
  }
}

fn quote_neut(ffi: FFI, size: Int, neut: Neut) -> Term {
  case neut {
    v.NVar(level) -> tm.Var(size - level - 1)
    v.NHole(id) -> tm.Hole(id)
    v.NApp(fun_neut, arg_val) -> {
      let fun = quote_neut(ffi, size, fun_neut)
      let arg = quote(ffi, size, arg_val)
      tm.App(False, fun, arg)
    }
    v.NMatch(env, arg_neut, cases) -> {
      let arg = quote_neut(ffi, size, arg_neut)
      let cases = list.map(cases, quote_case(ffi, env, _))
      tm.Match(arg, cases)
    }
    v.NCall(name, returns, args) -> {
      let returns = quote(ffi, size, returns)
      let args = list.map(args, quote(ffi, size, _))
      tm.Call(name, returns, args)
    }
  }
}

fn quote_case(ffi: FFI, env: Env, c: Case) -> Case {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  let #(guard, env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let env = v.env_push(env, list.length(tm.bindings(g_pattern)))
      let g_term = normalize(ffi, env, g_term)
      #(Some(#(g_term, g_pattern)), env)
    }
    None -> #(None, env)
  }
  let body = normalize(ffi, env, c.body)
  tm.Case(c.pattern, guard, body)
}
