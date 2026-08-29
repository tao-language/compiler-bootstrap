import core/context.{type Context, type Subst, Context}
import core/error.{type Error} as e
import core/ffi.{type FFI}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap, unwrap_seen}
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn context(ctx: Context) -> Context {
  let env = list.map(ctx.env, value(ctx.ffi, ctx.subst, _))
  let types =
    list.map(ctx.types, fn(name_type) {
      let #(name, type_) = name_type
      #(name, value(ctx.ffi, ctx.subst, type_))
    })
  Context(
    ..ctx,
    env: env,
    types: types,
    errors: list.map(ctx.errors, error(ctx.ffi, ctx.subst, ctx.env, _)),
  )
}

/// Resolve all holes in a term using the substitution.
///
/// The `seen` argument tracks hole IDs currently being resolved to detect
/// self-referential cycles. This happens when a term-level hole is unified
/// with a value (e.g., a Lam) whose body term still contains that same hole.
pub fn term(ffi: FFI, subst: Subst, size: Int, t: Term) -> Term {
  term_seen(ffi, subst, size, t, [])
}

fn term_seen(
  ffi: FFI,
  subst: Subst,
  size: Int,
  t: Term,
  seen: List(Int),
) -> Term {
  let self = fn(size, t) { term_seen(ffi, subst, size, t, seen) }
  case t {
    tm.Typ(_) -> t
    tm.Hole(None) -> t
    tm.Hole(Some(id)) ->
      // Cycle detection: if this hole is already being resolved,
      // return it as-is to break the infinite loop.
      case list.contains(seen, id) {
        True -> t
        False ->
          case list.key_find(subst, id) {
            Error(Nil) -> t
            Ok(value) -> {
              let value = unwrap(ffi, subst, value)
              let quoted = quote(ffi, size, value)
              // Add this hole ID to the seen set for this resolution chain.
              term_seen(ffi, subst, size, quoted, [id, ..seen])
            }
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
    tm.Call(name, ret, arg) -> {
      let ret = self(size, ret)
      let arg = self(size, arg)
      tm.Call(name, ret, arg)
    }
    tm.Ann(t, type_) -> {
      let t = self(size, t)
      let type_ = self(size, type_)
      tm.Ann(t, type_)
    }
    tm.For(#(name, param), body) -> {
      let param = self(size, param)
      let body = self(size + 1, body)
      tm.For(#(name, param), body)
    }
    tm.Lam(#(name, param), body) -> {
      let param = self(size, param)
      let body = self(size + 1, body)
      tm.Lam(#(name, param), body)
    }
    tm.Pi(#(name, domain), codomain) -> {
      let domain = self(size, domain)
      let codomain = self(size + 1, codomain)
      tm.Pi(#(name, domain), codomain)
    }
    tm.Fix(name, body) -> {
      let body = self(size + 1, body)
      tm.Fix(name, body)
    }
    tm.App(fun, arg) -> {
      let fun = self(size, fun)
      let arg = self(size, arg)
      tm.App(fun, arg)
    }
    tm.TypeDef(type_def) -> todo
    tm.Match(arg, cases) -> {
      let arg = self(size, arg)
      let cases = list.map(cases, resolve_case(ffi, subst, size, seen, _))
      tm.Match(arg, cases)
    }
    tm.Err -> t
  }
}

/// Resolve all holes in a value using the substitution.
///
/// See `value_seen/4` for cycle detection: a hole's captured environment may
/// contain the very value that holds the hole (module-scope holes capture the
/// module records, which hold the hole as a field), so resolving a hole can
/// re-encounter the same hole through its environment or its solution.
pub fn value(ffi: FFI, subst: Subst, val: Value) -> Value {
  value_seen(ffi, subst, val, [])
}

fn value_seen(ffi: FFI, subst: Subst, val: Value, seen: List(Int)) -> Value {
  let self = fn(v) { value_seen(ffi, subst, v, seen) }
  case val {
    // A hole is resolved with its ID pushed on the seen stack: its solution
    // and every captured environment it carries (NHole env, NMatch env, ...
    // through its unwrapped solution) are walked with the ID on the stack, so
    // any re-encounter of the hole is caught by the cycle guard.
    v.Neut(v.NHole(_, Some(id))) ->
      // Cycle detection: if this hole is already being resolved up the
      // stack (its solution or a captured environment references it
      // again), return it as-is to break the infinite loop.
      case list.contains(seen, id) {
        True -> val
        False -> {
          let resolved = unwrap_seen(ffi, subst, val, seen)
          let seen = [id, ..seen]
          case resolved {
            // If unwrap still returns a Neut, just resolve its parts.
            // No need to try to re-evaluate it into a concrete value.
            v.Neut(neut) -> v.Neut(neutral_seen(ffi, subst, neut, seen))
            solved -> value_seen(ffi, subst, solved, seen)
          }
        }
      }
    v.Neut(v.NHole(_, None)) -> {
      let resolved = unwrap_seen(ffi, subst, val, seen)
      case resolved {
        v.Neut(neut) -> v.Neut(neutral_seen(ffi, subst, neut, seen))
        solved -> value_seen(ffi, subst, solved, seen)
      }
    }
    v.Typ(u) -> v.Typ(u)
    v.Lit(k) -> v.Lit(k)
    v.LitT(k) -> v.LitT(k)
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
    // If unwrap still returns a Neut, just reolve its parts.
    // No need to try to re-evaluate it into a concrete value.
    v.Neut(neut) -> v.Neut(neutral_seen(ffi, subst, neut, seen))
    v.For(env, #(name, typ), body) -> {
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.For(env, #(name, self(typ)), body)
    }
    v.Lam(env, #(name, typ), body) -> {
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Lam(env, #(name, self(typ)), body)
    }
    v.Pi(env, #(name, typ), body) -> {
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Pi(env, #(name, self(typ)), body)
    }
    v.Fix(env, name, body) -> {
      let body = term(ffi, subst, list.length(env) + 1, body)
      v.Fix(env, name, body)
    }
    v.TypeDef(env, type_def) -> todo
    v.Err -> v.Err
  }
}

fn neutral_seen(ffi: FFI, subst: Subst, neut: Neut, seen: List(Int)) -> Neut {
  case neut {
    v.NVar(lvl) -> v.NVar(lvl)
    v.NHole(env, id) -> v.NHole(env, id)
    v.NApp(fun_neut, arg) -> {
      let fun_neut = neutral_seen(ffi, subst, fun_neut, seen)
      let arg = value_seen(ffi, subst, arg, seen)
      v.NApp(fun_neut, arg)
    }
    v.NMatch(env, arg_neut, cases) -> {
      let arg_neut = neutral_seen(ffi, subst, arg_neut, seen)
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
    v.NCall(name, ret, arg) -> {
      let ret = value_seen(ffi, subst, ret, seen)
      let arg = value_seen(ffi, subst, arg, seen)
      v.NCall(name, ret, arg)
    }
  }
}

pub fn error(ffi: FFI, subst: Subst, env: Env, err: Error) -> Error {
  let data = case err.data {
    // Syntax errors carry no values or terms to resolve.
    e.UnexpectedToken(x) -> e.UnexpectedToken(x)
    e.ExpectedToken(x, y) -> e.ExpectedToken(x, y)
    e.UnexpectedEndOfInput -> e.UnexpectedEndOfInput
    e.SyntaxError(message) -> e.SyntaxError(message)
    // Type-checking errors
    e.VarUndefined(x) -> e.VarUndefined(x)
    e.TypeMismatch(#(a, s1), #(b, s2)) -> {
      let a = value(ffi, subst, a)
      let b = value(ffi, subst, b)
      e.TypeMismatch(#(a, s1), #(b, s2))
    }
    e.InfiniteType(id, a) -> {
      let a = value(ffi, subst, a)
      e.InfiniteType(id, a)
    }
    e.RcdFieldNotFound(field) -> e.RcdFieldNotFound(field)
    e.NotAFunction(fun, fun_type) -> {
      let fun = term(ffi, subst, list.length(env), fun)
      let fun_type = value(ffi, subst, fun_type)
      e.NotAFunction(fun, fun_type)
    }
    e.AppExpectedExplicitArg(fun_type) -> {
      let fun_type = value(ffi, subst, fun_type)
      e.AppExpectedExplicitArg(fun_type)
    }
    // The variant terms are left unresolved for now.
    e.TypeVariantUndefined(tag, variants) ->
      e.TypeVariantUndefined(tag, variants)
  }
  e.Error(..err, data: data)
}

fn resolve_case(
  ffi: FFI,
  subst: Subst,
  size: Int,
  seen: List(Int),
  c: Case,
) -> Case {
  let size = size + list.length(tm.bindings(c.pattern))
  let #(guard, size) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let size = size + list.length(tm.bindings(g_pattern))
      let g_term = term_seen(ffi, subst, size, g_term, seen)
      #(Some(#(g_term, g_pattern)), size)
    }
    None -> #(None, size)
  }
  tm.Case(c.pattern, guard, term_seen(ffi, subst, size, c.body, seen))
}
