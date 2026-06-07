/// Quote — Convert Values back to Terms
import core/context.{type FFI}
import core/eval.{eval}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn quote(ffi: FFI, size: Int, value: Value) -> Term {
  case value {
    v.Typ(universe) -> tm.Typ(universe)
    v.Lit(lit) -> tm.Lit(lit)
    v.LitT(lit) -> tm.LitT(lit)
    v.Ctr(tag, arg_val) -> tm.Ctr(tag, quote(ffi, size, arg_val))
    v.Rcd(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, value) = field
          #(name, quote(ffi, size, value))
        })
      tm.Rcd(fields)
    }
    v.RcdT(fields_val) -> {
      let fields =
        list.map(fields_val, fn(field) {
          let #(name, #(value, default_val)) = field
          let default = option.map(default_val, fn(v) { quote(ffi, size, v) })
          #(name, #(quote(ffi, size, value), default))
        })
      tm.RcdT(fields)
    }
    v.Neut(neut) -> quote_neut(ffi, size, neut)
    v.Lam(env, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let env = v.env_push(env, 1)
      let body_val = eval(ffi, env, body)
      let body = quote(ffi, list.length(env), body_val)
      tm.Lam(#(name, param), body)
    }
    v.Pi(env, implicit, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let env = v.env_push(env, 1)
      let body_val = eval(ffi, env, body)
      let body = quote(ffi, list.length(env), body_val)
      tm.Pi(implicit, #(name, param), body)
    }
    v.Fix(env, name, body) -> {
      let env = v.env_push(env, 1)
      let body_val = eval(ffi, env, body)
      let body = quote(ffi, list.length(env), body_val)
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
    v.NApp(fun_neut, arg) -> todo
    v.NMatch(env, arg_neut, cases) -> {
      let arg = quote_neut(ffi, size, arg_neut)
      let cases = list.map(cases, quote_case(ffi, env, _))
      tm.Match(arg, cases)
    }
    v.NCall(name, args) -> todo
  }
}

fn quote_case(ffi: FFI, env: Env, c: Case) -> Case {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  let #(guard, env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let env = v.env_push(env, list.length(tm.bindings(g_pattern)))
      let g_term_val = eval(ffi, env, g_term)
      let g_term = quote(ffi, list.length(env), g_term_val)
      #(Some(#(g_term, g_pattern)), env)
    }
    None -> #(None, env)
  }
  let body_val = eval(ffi, env, c.body)
  let body = quote(ffi, list.length(env), body_val)
  tm.Case(c.pattern, guard, body)
}
