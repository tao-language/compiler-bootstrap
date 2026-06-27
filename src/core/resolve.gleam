import core/context.{type Context, type Subst, Context}
import core/error.{type Error}
import core/eval.{eval}
import core/ffi.{type FFI}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Value}
import gleam/list
import gleam/option.{None, Some}

pub fn context(ctx: Context) -> Context {
  Context(
    ..ctx,
    env: list.map(ctx.env, value(ctx.ffi, ctx.subst, ctx.env, _)),
    types: list.map(ctx.types, fn(name_type) {
      let #(name, type_) = name_type
      #(name, value(ctx.ffi, ctx.subst, ctx.env, type_))
    }),
    errors: list.map(ctx.errors, error(ctx.ffi, ctx.subst, ctx.env, _)),
  )
}

pub fn term(ffi: FFI, subst: Subst, size: Int, t: Term) -> Term {
  case t {
    tm.Typ(_) -> t
    tm.Hole(id) ->
      case list.key_find(subst, id) {
        Error(Nil) -> t
        Ok(value) -> {
          let value = unwrap(ffi, subst, value)
          let t = quote(ffi, size, value)
          term(ffi, subst, size, t)
        }
      }
    tm.Lit(_) -> t
    tm.LitT(_) -> t
    tm.Var(_) -> t
    tm.Ctr(tag, arg) -> tm.Ctr(tag, term(ffi, subst, size, arg))
    tm.Rcd(fields, tail) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(v, t)) = field
          let v = term(ffi, subst, size, v)
          let t = option.map(t, term(ffi, subst, size, _))
          #(name, #(v, t))
        })
      let tail = option.map(tail, term(ffi, subst, size, _))
      tm.Rcd(fields, tail)
    }
    tm.Call(name, returns, args) -> {
      let returns = term(ffi, subst, size, returns)
      let args = list.map(args, term(ffi, subst, size, _))
      tm.Call(name, returns, args)
    }
    tm.Ann(t, type_) -> {
      let t = term(ffi, subst, size, t)
      let type_ = term(ffi, subst, size, type_)
      tm.Ann(t, type_)
    }
    tm.Lam(implicit, #(name, param), body) -> {
      let param = term(ffi, subst, size, param)
      let body = term(ffi, subst, size, body)
      tm.Lam(implicit, #(name, param), body)
    }
    tm.Pi(implicit, #(name, domain), codomain) -> {
      let domain = term(ffi, subst, size, domain)
      let codomain = term(ffi, subst, size, codomain)
      tm.Pi(implicit, #(name, domain), codomain)
    }
    tm.Fix(name, body) -> {
      let body = term(ffi, subst, size, body)
      tm.Fix(name, body)
    }
    tm.App(implicit, fun, arg) -> {
      let fun = term(ffi, subst, size, fun)
      let arg = term(ffi, subst, size, arg)
      tm.App(implicit, fun, arg)
    }
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> {
      let arg = term(ffi, subst, size, arg)
      let cases = list.map(cases, resolve_case(ffi, subst, size, _))
      tm.Match(arg, cases)
    }
    tm.Err -> t
  }
}

pub fn value(ffi: FFI, subst: Subst, env: Env, val: Value) -> Value {
  let size = list.length(env)
  quote(ffi, size, val)
  |> term(ffi, subst, size, _)
  |> eval(ffi, env, _)
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
