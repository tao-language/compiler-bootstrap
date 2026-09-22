import core/context.{type Context, type Subst, Context, with_err}
import core/error as e
import core/eval.{eval}
import core/ffi.{type FFI}
import core/quote.{quote}
import core/term.{type Case, type Term} as tm
import core/unify.{unify}
import core/unwrap.{unwrap, unwrap_seen}
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

/// Finalize a context after type checking: discharge every leftover
/// deferred constraint, then resolve every hole in the environment, the
/// type bindings, and the accumulated errors.
pub fn context(ctx: Context) -> Context {
  let ctx = discharge(ctx.deferred, ctx)
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
pub fn term(ffi: FFI, subst: Subst, env: Env, t: Term) -> Term {
  term_seen(ffi, subst, env, t, [])
}

fn term_seen(
  ffi: FFI,
  subst: Subst,
  env: Env,
  t: Term,
  seen: List(Int),
) -> Term {
  let self = fn(env, t) { term_seen(ffi, subst, env, t, seen) }
  case t {
    tm.Hole(Some(id)) ->
      // Cycle detection: if this hole is already being resolved,
      // return it as-is to break the infinite loop.
      case list.contains(seen, id) {
        True -> t
        False ->
          case list.key_find(subst, id) {
            Error(Nil) -> t
            Ok(#(env_h, value)) -> {
              let value = unwrap(ffi, subst, value)
              // Quote against the env captured when the hole was solved,
              // not the term's frame: the solution's variable levels are
              // relative to the solve-time frame, which may contain
              // bindings absent from the term's (shorter) frame.
              let quoted = quote(ffi, env_h, value)
              // Add this hole ID to the seen set for this resolution
              // chain, continuing the walk in the captured frame: the
              // quoted term's indices are relative to `env_h`.
              term_seen(ffi, subst, env_h, quoted, [id, ..seen])
            }
          }
      }
    tm.Ctr(tag, arg) -> tm.Ctr(tag, self(env, arg))
    tm.Rcd(fields, tail) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, #(v, t)) = field
          let v = self(env, v)
          let t = option.map(t, self(env, _))
          #(name, #(v, t))
        })
      let tail = option.map(tail, self(env, _))
      tm.Rcd(fields, tail)
    }
    tm.Call(name, ret, arg) -> {
      let ret = self(env, ret)
      let arg = self(env, arg)
      tm.Call(name, ret, arg)
    }
    tm.Ann(t, type_) -> {
      let t = self(env, t)
      let type_ = self(env, type_)
      tm.Ann(t, type_)
    }
    tm.For(#(name, param), body) -> {
      let param = self(env, param)
      let body = self(v.env_push(env, 1), body)
      tm.For(#(name, param), body)
    }
    tm.Lam(#(name, param), body) -> {
      let param = self(env, param)
      let body = self(v.env_push(env, 1), body)
      tm.Lam(#(name, param), body)
    }
    tm.Pi(#(name, domain), codomain) -> {
      let domain = self(env, domain)
      let codomain = self(v.env_push(env, 1), codomain)
      tm.Pi(#(name, domain), codomain)
    }
    tm.Fix(name, body) -> {
      let body = self(v.env_push(env, 1), body)
      tm.Fix(name, body)
    }
    tm.App(fun, arg) -> {
      let fun = self(env, fun)
      let arg = self(env, arg)
      tm.App(fun, arg)
    }
    // Type definitions: the argument and variant terms index into
    // frames with the parameters bound (and, per variant, the variant's
    // own parameters bound innermost); the parameter types live in the
    // surrounding frame.
    tm.TypeDef(tm.TypeDefinition(params, arg, variants)) -> {
      let p_env = v.env_push(env, list.length(params))
      let params =
        list.map(params, fn(param) {
          let #(name, typ) = param
          #(name, self(env, typ))
        })
      let arg = self(p_env, arg)
      let variants =
        list.map(variants, fn(variant) {
          let #(tag, tm.Variant(vparams, varg, vret)) = variant
          let vp_env = v.env_push(p_env, list.length(vparams))
          let vparams =
            list.map(vparams, fn(param) {
              let #(name, typ) = param
              #(name, self(p_env, typ))
            })
          #(tag, tm.Variant(vparams, self(vp_env, varg), self(vp_env, vret)))
        })
      tm.TypeDef(tm.TypeDefinition(params, arg, variants))
    }
    tm.Match(arg, cases) -> {
      let arg = self(env, arg)
      let cases = list.map(cases, resolve_case(ffi, subst, env, seen, _))
      tm.Match(arg, cases)
    }
    // Typ, Hole(None), Lit, LitT, Var and Err carry no holes to resolve.
    _ -> t
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
    // A named hole is resolved with its ID pushed on the seen stack: its solution
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
    // If unwrap still returns a Neut, just resolve its parts.
    // No need to try to re-evaluate it into a concrete value.
    v.Neut(neut) -> v.Neut(neutral_seen(ffi, subst, neut, seen))
    v.For(env, #(name, typ), body) -> {
      let body = term(ffi, subst, v.env_push(env, 1), body)
      v.For(env, #(name, self(typ)), body)
    }
    v.Lam(env, #(name, typ), body) -> {
      let body = term(ffi, subst, v.env_push(env, 1), body)
      v.Lam(env, #(name, self(typ)), body)
    }
    v.Pi(env, #(name, typ), body) -> {
      let body = term(ffi, subst, v.env_push(env, 1), body)
      v.Pi(env, #(name, self(typ)), body)
    }
    v.Fix(env, name, body) -> {
      let body = term(ffi, subst, v.env_push(env, 1), body)
      v.Fix(env, name, body)
    }
    v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> {
      // As in `term_seen`: the inner terms index into frames with the
      // parameters bound; the captured environment is left as is (the
      // entries' holes are resolved where they occur).
      let p_env = v.env_push(env, list.length(params))
      let params =
        list.map(params, fn(param) {
          let #(name, typ) = param
          #(name, self(typ))
        })
      let arg = term(ffi, subst, p_env, arg)
      let variants =
        list.map(variants, fn(variant) {
          let #(tag, v.Variant(vparams, varg, vret)) = variant
          let vp_env = v.env_push(p_env, list.length(vparams))
          let vparams =
            list.map(vparams, fn(param) {
              let #(name, typ) = param
              #(name, self(typ))
            })
          #(
            tag,
            v.Variant(
              vparams,
              term(ffi, subst, vp_env, varg),
              term(ffi, subst, vp_env, vret),
            ),
          )
        })
      v.TypeDef(env, v.TypeDefinition(params, arg, variants))
    }
    // Typ, Lit, LitT and Err carry no holes to resolve.
    _ -> val
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
    v.NMatch(captured_env, arg, cases) -> {
      let arg = value_seen(ffi, subst, arg, seen)
      let cases =
        list.map(cases, fn(c) {
          resolve_case(ffi, subst, captured_env, seen, c)
        })
      v.NMatch(captured_env, arg, cases)
    }
    v.NCall(name, ret, arg) -> {
      let ret = value_seen(ffi, subst, ret, seen)
      let arg = value_seen(ffi, subst, arg, seen)
      v.NCall(name, ret, arg)
    }
  }
}

/// Resolve hole references inside the values carried by an error, so
/// displayed types show their solutions rather than `?n`.
pub fn error(ffi: FFI, subst: Subst, env: Env, err: e.Error) -> e.Error {
  let data = case err.data {
    // Only the errors carrying values or terms need resolving.
    e.TypeMismatch(#(a, s1), #(b, s2)) -> {
      let a = value(ffi, subst, a)
      let b = value(ffi, subst, b)
      e.TypeMismatch(#(a, s1), #(b, s2))
    }
    e.InfiniteType(id, a) -> {
      let a = value(ffi, subst, a)
      e.InfiniteType(id, a)
    }
    e.NotAFunction(fun, fun_type) -> {
      let fun = term(ffi, subst, env, fun)
      let fun_type = value(ffi, subst, fun_type)
      e.NotAFunction(fun, fun_type)
    }
    e.AppExpectedExplicitArg(fun_type) -> {
      let fun_type = value(ffi, subst, fun_type)
      e.AppExpectedExplicitArg(fun_type)
    }
    e.MatchGuardMismatch(guard, span) -> {
      e.MatchGuardMismatch(term(ffi, subst, env, guard), span)
    }
    // Syntax errors, VarUndefined, RcdFieldNotFound and
    // TypeVariantUndefined (whose variant terms are left unresolved for
    // now) carry nothing to resolve.
    _ -> err.data
  }
  e.Error(..err, data: data)
}

/// Discharge every leftover deferred constraint — a pair the unifier
/// recorded while a side was still neutral and the retries never decided.
/// Each leftover is discharged with per-neutral semantics, not errored
/// outright:
///
/// * `NMatch` vs concrete: the match has the expected type if *some* case
///   body has it (exists semantics — the scrutinee is neutral, so any
///   case may be the one selected; a dependent dispatch whose cases
///   intentionally differ must pass).
/// * `NCall` vs concrete: the declared return type is unified with the
///   expected value.
/// * `NVar`/`NApp`/unsolved `NHole` vs concrete: accepted. A rigid
///   variable's binding type is a dependent fact the value unifier cannot
///   decide (e.g. an overloaded operator's `__type` vs the argument
///   record), so it is left standing without an error.
/// * Two neutrals: accepted (nothing to decide).
///
/// Admitted unsoundnesses (pinned in the `known_unsound_*` tests): exists
/// semantics silently drops *incompatible* case bodies (a neutral match
/// with one `Bool` and one `Int` body type-checks against `Int`), and a
/// case body that is itself neutral (an overload dispatch) re-defers
/// without ever checking the `NCall`'s declared return type.
fn discharge(
  deferred: List(#(#(v.Value, Span), #(v.Value, Span))),
  ctx: Context,
) -> Context {
  list.fold(deferred, ctx, fn(acc, pair) { discharge_pair(acc, pair) })
}

fn discharge_pair(
  ctx: Context,
  pair: #(#(v.Value, Span), #(v.Value, Span)),
) -> Context {
  let #(#(a, sa), #(b, sb)) = pair
  case unwrap(ctx.ffi, ctx.subst, a), unwrap(ctx.ffi, ctx.subst, b) {
    v.Neut(neut), b -> discharge_neut(ctx, neut, sa, b, sb)
    a, v.Neut(neut) -> discharge_neut(ctx, neut, sb, a, sa)
    // Both sides concrete: already decided by the retry; nothing to do.
    _, _ -> ctx
  }
}

fn discharge_neut(
  ctx: Context,
  neut: Neut,
  neut_span: Span,
  val: v.Value,
  val_span: Span,
) -> Context {
  case neut {
    // Binding types are dependent facts this unifier cannot decide
    // (see the `discharge` docs): accept.
    v.NVar(_) -> ctx
    v.NApp(_, _) -> ctx
    v.NHole(_, _) -> ctx
    v.NCall(_, ret, _) -> unify(ctx, #(ret, neut_span), #(val, val_span))
    // A neutral match has the expected type if some case body has it.
    v.NMatch(env, _, cases) ->
      discharge_match(ctx, env, cases, neut_span, val, val_span)
  }
}

/// Check the expected value against some case body of a neutral match.
/// Each case is tried so an incompatible case leaks no errors; the first
/// case that unifies cleanly is committed. If no case is compatible,
/// report a `TypeMismatch` against the first body.
fn discharge_match(
  ctx: Context,
  env: Env,
  cases: List(Case),
  s: Span,
  val: v.Value,
  vs: Span,
) -> Context {
  case discharge_match_case(ctx, env, cases, s, val, vs) {
    Some(ctx) -> ctx
    None ->
      case cases {
        [] -> ctx
        [c, ..] -> {
          let env = v.env_push(env, case_vars(c))
          let body = eval(ctx.ffi, env, c.body)
          with_err(ctx, e.TypeMismatch(#(body, s), #(val, vs)), s)
        }
      }
  }
}

fn discharge_match_case(
  ctx: Context,
  env: Env,
  cases: List(Case),
  s: Span,
  val: v.Value,
  vs: Span,
) -> Option(Context) {
  case cases {
    [] -> None
    [c, ..cases] -> {
      let env = v.env_push(env, case_vars(c))
      let body = eval(ctx.ffi, env, c.body)
      let num_errors = list.length(ctx.errors)
      let ctx_try = unify(ctx, #(body, s), #(val, vs))
      case list.length(ctx_try.errors) > num_errors {
        True -> discharge_match_case(ctx, env, cases, s, val, vs)
        False -> Some(ctx_try)
      }
    }
  }
}

/// Number of variables bound by a case's pattern and guard pattern.
fn case_vars(c: Case) -> Int {
  let n = list.length(tm.bindings(c.pattern))
  case c.guard {
    None -> n
    Some(#(_, g_pattern)) -> n + list.length(tm.bindings(g_pattern))
  }
}

fn resolve_case(
  ffi: FFI,
  subst: Subst,
  env: Env,
  seen: List(Int),
  c: Case,
) -> Case {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  let #(guard, env) = case c.guard {
    Some(#(g_term, g_pattern)) -> {
      let env = v.env_push(env, list.length(tm.bindings(g_pattern)))
      let g_term = term_seen(ffi, subst, env, g_term, seen)
      #(Some(#(g_term, g_pattern)), env)
    }
    None -> #(None, env)
  }
  tm.Case(c.pattern, guard, term_seen(ffi, subst, env, c.body, seen))
}
