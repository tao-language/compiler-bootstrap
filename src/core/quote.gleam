/// Quote — Convert Values back to Terms
import core/eval.{eval}
import core/state.{type FFI}
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
          let #(name, value, default_val) = field
          let default = option.map(default_val, fn(v) { quote(ffi, size, v) })
          #(name, quote(ffi, size, value), default)
        })
      tm.RcdT(fields)
    }
    v.Neut(neut) -> quote_neut(ffi, size, neut)
    v.Lam(implicit, #(name, param_val), #(env, body)) -> {
      let param = quote(ffi, size, param_val)
      let body_val = eval(ffi, [param_val, ..env], body)
      let body = quote(ffi, size, body_val)
      tm.Lam(implicit, #(name, param), body)
    }
    v.Pi(implicit, #(name, param_val), #(env, body)) -> {
      let param = quote(ffi, size, param_val)
      let body_val = eval(ffi, [param_val, ..env], body)
      let body = quote(ffi, size, body_val)
      tm.Pi(implicit, #(name, param), body)
    }
    v.Fix(name, #(env, body)) -> {
      todo
    }
    v.Union(variants) -> {
      todo
    }
    v.Err -> tm.Err
  }
}

fn quote_neut(ffi: FFI, size: Int, neut: Neut) -> Term {
  case neut {
    v.NVar(level) -> tm.Var(size - level - 1)
    v.NHole(id) -> tm.Hole(id)
    _ -> {
      echo neut
      todo
    }
  }
}
