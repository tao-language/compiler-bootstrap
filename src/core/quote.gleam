/// Quote — Convert Values back to Terms
import core/eval.{eval}
import core/ffi.{type FFI}
import core/term.{type Case, type Term} as tm
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}

fn normalize_term(ffi: FFI, env: Env, term: Term) -> Term {
  eval(ffi, env, term)
  |> quote(ffi, list.length(env), _)
}

fn find_index(env: Env, target: v.Value) -> Option(Int) {
  case env {
    [] -> None
    [val, ..rest] if val == target -> Some(0)
    [_, ..rest] -> {
      case find_index(rest, target) {
        Some(i) -> Some(i + 1)
        None -> None
      }
    }
  }
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
    v.Neut(neut) -> quote_neut(ffi, [], neut)
    v.Lam(env, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let body = normalize_term(ffi, v.env_push(env, 1), body)
      tm.Lam(False, #(name, param), body)
    }
    v.Pi(env, implicit, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let body = normalize_term(ffi, v.env_push(env, 1), body)
      tm.Pi(implicit, #(name, param), body)
    }
    v.Fix(env, name, body) -> {
      let body = normalize_term(ffi, v.env_push(env, 1), body)
      tm.Fix(name, body)
    }
    v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> {
      todo
    }
    v.Err -> tm.Err
  }
}

fn quote_neut(ffi: FFI, env: Env, neut: Neut) -> Term {
  case neut {
    v.NVar(level) -> tm.Var(list.length(env) - level - 1)
    v.NHole(id) -> {
      // Try to find the hole in the captured env and quote as a Var.
      // This handles param holes that were filled during Pi application
      // but whose term-level hole IDs have no substitution entries.
      case find_index(env, v.hole(id)) {
        Some(index) -> tm.Var(index)
        None -> tm.Hole(id)
      }
    }
    v.NApp(fun_neut, arg_val) -> {
      let fun = quote_neut(ffi, env, fun_neut)
      let arg = quote(ffi, list.length(env), arg_val)
      tm.App(False, fun, arg)
    }
    v.NMatch(captured_env, arg_neut, cases) -> {
      let arg = quote_neut(ffi, captured_env, arg_neut)
      let cases = list.map(cases, quote_case(ffi, captured_env, _))
      tm.Match(arg, cases)
    }
    v.NCall(name, returns, args) -> {
      let returns = quote(ffi, list.length(env), returns)
      let args = list.map(args, quote(ffi, list.length(env), _))
      tm.Call(name, returns, args)
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
