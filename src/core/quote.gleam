/// Quote — Convert Values back to Terms
import core/context.{type FFI}
import core/eval.{eval}
import core/term.{type Term} as tm
import core/value.{type Neut, type Value} as v
import gleam/list
import gleam/option

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
      let body_val = eval(ffi, [v.var(list.length(env)), ..env], body)
      let body = quote(ffi, size + 1, body_val)
      tm.Lam(#(name, param), body)
    }
    v.Pi(env, implicit, #(name, param_val), body) -> {
      let param = quote(ffi, size, param_val)
      let body_val = eval(ffi, [v.var(list.length(env)), ..env], body)
      let body = quote(ffi, size + 1, body_val)
      tm.Pi(implicit, #(name, param), body)
    }
    v.Fix(env, name, body) -> {
      let body_val = eval(ffi, [v.var(list.length(env)), ..env], body)
      let body = quote(ffi, size + 1, body_val)
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
      // TODO: eval+quote cases with env
      tm.Match(arg, cases)
    }
    v.NCall(name, args) -> todo
  }
}
