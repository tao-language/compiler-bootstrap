import core/context.{type Subst}
import core/eval.{eval}
import core/ffi.{type FFI}
import core/parse
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap_neut}
import core/value.{type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn resolve(ffi: FFI, subst: Subst, size: Int, term: Term) -> Term {
  case term {
    tm.Typ(_) -> term
    tm.Hole(id) ->
      case list.key_find(subst, id) {
        Error(Nil) -> term
        Ok(value) -> {
          let term = quote(ffi, size, value)
          resolve(ffi, subst, size, term)
        }
      }
    tm.Lit(_) -> term
    tm.LitT(_) -> term
    tm.Var(_) -> term
    tm.Ctr(tag, arg) -> tm.Ctr(tag, resolve(ffi, subst, size, arg))
    tm.Rcd(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, term) = field
          #(name, resolve(ffi, subst, size, term))
        })
      tm.Rcd(fields)
    }
    tm.RcdT(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(term, default)) = field
          let term = resolve(ffi, subst, size, term)
          let default = option.map(default, resolve(ffi, subst, size, _))
          #(name, #(term, default))
        })
      tm.RcdT(fields)
    }
    tm.Call(name, returns, args) -> {
      let returns = resolve(ffi, subst, size, returns)
      let args = list.map(args, resolve(ffi, subst, size, _))
      tm.Call(name, returns, args)
    }
    tm.Ann(term, type_) -> {
      let term = resolve(ffi, subst, size, term)
      let type_ = resolve(ffi, subst, size, type_)
      tm.Ann(term, type_)
    }
    tm.Lam(implicit, #(name, param), body) -> {
      let param = resolve(ffi, subst, size, param)
      let body = resolve(ffi, subst, size, body)
      tm.Lam(implicit, #(name, param), body)
    }
    tm.Pi(implicit, #(name, domain), codomain) -> {
      let domain = resolve(ffi, subst, size, domain)
      let codomain = resolve(ffi, subst, size, codomain)
      tm.Pi(implicit, #(name, domain), codomain)
    }
    tm.Fix(name, body) -> {
      let body = resolve(ffi, subst, size, body)
      tm.Fix(name, body)
    }
    tm.App(implicit, fun, arg) -> {
      let fun = resolve(ffi, subst, size, fun)
      let arg = resolve(ffi, subst, size, arg)
      tm.App(implicit, fun, arg)
    }
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> {
      let arg = resolve(ffi, subst, size, arg)
      let cases = list.map(cases, resolve_case(ffi, subst, size, _))
      tm.Match(arg, cases)
    }
    tm.Err -> term
  }
}

pub fn resolve_value(ffi: FFI, subst: Subst, size: Int, value: Value) -> Value {
  case value {
    v.Typ(_) -> value
    v.Lit(_) -> value
    v.LitT(_) -> value
    v.Ctr(tag, arg) -> {
      let arg = resolve_value(ffi, subst, size, arg)
      v.Ctr(tag, arg)
    }
    v.Rcd(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, value) = field
          let value = resolve_value(ffi, subst, size, value)
          #(name, value)
        })
      v.Rcd(fields)
    }
    v.RcdT(fields) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(type_, opt_default)) = field
          let type_ = resolve_value(ffi, subst, size, type_)
          let opt_default =
            option.map(opt_default, resolve_value(ffi, subst, size, _))
          #(name, #(type_, opt_default))
        })
      v.RcdT(fields)
    }
    v.Neut(neutral) -> unwrap_neut(ffi, subst, neutral)
    v.Lam(env, param, body) -> todo
    v.Pi(env, implicit, domain, codomain) -> todo
    v.Fix(env, name, body) -> todo
    v.TypeDef(env, type_def) -> todo
    v.Err -> todo
  }
}

pub fn resolve_case(ffi: FFI, subst: Subst, size: Int, c: Case) -> Case {
  let size = size + list.length(tm.bindings(c.pattern))
  let #(guard, size) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let size = size + list.length(tm.bindings(g_pattern))
      let g_term = resolve(ffi, subst, size, g_term)
      #(Some(#(g_term, g_pattern)), size)
    }
    None -> #(None, size)
  }
  tm.Case(c.pattern, guard, resolve(ffi, subst, size, c.body))
}
