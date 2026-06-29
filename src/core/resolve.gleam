import core/context.{type Context, type Subst, Context}
import core/error.{type Error}
import core/ffi.{type FFI}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap, unwrap_neut}
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn context(ctx: Context) -> Context {
  Context(
    ..ctx,
    env: list.map(ctx.env, value(ctx.ffi, ctx.subst, _)),
    types: list.map(ctx.types, fn(name_type) {
      let #(name, type_) = name_type
      #(name, value(ctx.ffi, ctx.subst, type_))
    }),
    errors: list.map(ctx.errors, error(ctx.ffi, ctx.subst, ctx.env, _)),
  )
}

pub fn term(ffi: FFI, subst: Subst, size: Int, t: Term) -> Term {
  let self = fn(size, t) { term(ffi, subst, size, t) }
  case t {
    tm.Typ(_) -> t
    tm.Hole(id) ->
      case list.key_find(subst, id) {
        Error(Nil) -> t
        Ok(value) -> {
          let value = unwrap(ffi, subst, value)
          self(size, quote(ffi, size, value))
        }
      }
    tm.Lit(_) -> t
    tm.LitT(_) -> t
    tm.Var(_) -> t
    tm.Ctr(tag, arg) -> tm.Ctr(tag, self(size, arg))
    tm.Rcd(fields, tail) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(v, t)) = field
          let v = self(size, v)
          let t = option.map(t, self(size, _))
          #(name, #(v, t))
        })
      let tail = option.map(tail, self(size, _))
      tm.Rcd(fields, tail)
    }
    tm.Call(name, returns, args) -> {
      let returns = self(size, returns)
      let args = list.map(args, self(size, _))
      tm.Call(name, returns, args)
    }
    tm.Ann(t, type_) -> {
      let t = self(size, t)
      let type_ = self(size, type_)
      tm.Ann(t, type_)
    }
    tm.Lam(implicit, #(name, param), body) -> {
      let param = self(size, param)
      let body = self(size + 1, body)
      tm.Lam(implicit, #(name, param), body)
    }
    tm.Pi(implicit, #(name, domain), codomain) -> {
      let domain = self(size, domain)
      let codomain = self(size + 1, codomain)
      tm.Pi(implicit, #(name, domain), codomain)
    }
    tm.Fix(name, body) -> {
      let body = self(size + 1, body)
      tm.Fix(name, body)
    }
    tm.App(implicit, fun, arg) -> {
      let fun = self(size, fun)
      let arg = self(size, arg)
      tm.App(implicit, fun, arg)
    }
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> {
      let arg = self(size, arg)
      let cases = list.map(cases, resolve_case(ffi, subst, size, _))
      tm.Match(arg, cases)
    }
    tm.Err -> t
  }
}

pub fn value(ffi: FFI, subst: Subst, val: Value) -> Value {
  let self = fn(v) { value(ffi, subst, v) }
  let val = unwrap(ffi, subst, val)
  case val {
    v.Typ(_) -> val
    v.Lit(_) -> val
    v.LitT(_) -> val
    v.Ctr(tag, arg) -> v.Ctr(tag, self(arg))
    v.Rcd(fields, tail) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(val, default)) = field
          let val = self(val)
          let default = option.map(default, self)
          #(name, #(val, default))
        })
      let tail = option.map(tail, self)
      v.Rcd(fields, tail)
    }
    v.Neut(neut) -> v.Neut(neutral(ffi, subst, neut))
    v.Lam(env, #(name, typ), body) -> {
      let env = list.map(env, self)
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Lam(env, #(name, self(typ)), body)
    }
    v.Pi(env, implicit, #(name, typ), body) -> {
      let env = list.map(env, self)
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Pi(env, implicit, #(name, self(typ)), body)
    }
    v.Fix(env, name, body) -> {
      let env = list.map(env, self)
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Fix(env, name, body)
    }
    v.TypeDef(env, type_def) -> todo
    v.Err -> val
  }
}

fn neutral(ffi: FFI, subst: Subst, neut: Neut) -> Neut {
  case neut {
    v.NVar(_) -> neut
    v.NHole(_) -> neut
    v.NApp(fun_nuet, arg) -> {
      let arg = value(ffi, subst, arg)
      v.NApp(fun_nuet, arg)
    }
    v.NMatch(env, arg_neut, cases) -> {
      let cases =
        list.map(cases, fn(c) {
          let size = list.length(env) + list.length(tm.bindings(c.pattern))
          let #(guard, size) = case c.guard {
            Some(#(cond, pattern)) -> {
              let cond = term(ffi, subst, size, cond)
              let size = size + list.length(tm.bindings(pattern))
              #(Some(#(cond, pattern)), size)
            }
            None -> #(None, 0)
          }
          let body = term(ffi, subst, size, c.body)
          tm.Case(c.pattern, guard, body)
        })
      v.NMatch(env, arg_neut, cases)
    }
    v.NCall(name, returns, args) -> {
      let returns = value(ffi, subst, returns)
      let args = list.map(args, value(ffi, subst, _))
      v.NCall(name, returns, args)
    }
  }
}

pub fn error(ffi: FFI, subst: Subst, env: Env, err: Error) -> Error {
  // todo
  err
}

fn resolve_case(ffi: FFI, subst: Subst, size: Int, c: Case) -> Case {
  let size = size + list.length(tm.bindings(c.pattern))
  let #(guard, size) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let size = size + list.length(tm.bindings(g_pattern))
      let g_term = term(ffi, subst, size, g_term)
      #(Some(#(g_term, g_pattern)), size)
    }
    None -> #(None, size)
  }
  tm.Case(c.pattern, guard, term(ffi, subst, size, c.body))
}
