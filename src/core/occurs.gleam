import core/context.{type Context}
import core/eval.{eval}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}

// TODO: replace ctx with only ffi, do not unwrap

/// Depth bound for the occurs check. A prospective solution that
/// re-introduces itself through its captured environment (a cyclic module
/// record) deepens the check by one level per `occurs` → `eval` → `occurs`
/// round, so a finite bound turns the non-termination into an
/// (over-conservative) `InfiniteType` error instead of a hang.
const occurs_depth_limit = 200

/// Check whether a hole occurs inside its own prospective solution.
/// Called before solving; a positive result is an infinite type.
pub fn occurs(ctx: Context, hole_id: Int, value: Value) -> Bool {
  occurs_rec(ctx, hole_id, value, 0)
}

fn occurs_rec(ctx: Context, hole_id: Int, value: Value, depth: Int) -> Bool {
  case depth > occurs_depth_limit {
    True -> True
    False -> {
      case unwrap(ctx.ffi, ctx.subst, value) {
        v.Typ(_) -> False
        v.Lit(_) -> False
        v.LitT(_) -> False
        v.Ctr(_, arg) -> occurs_rec(ctx, hole_id, arg, depth + 1)
        v.Rcd(fields, tail) ->
          list.any(fields, fn(field) {
            let #(_, #(val, default)) = field
            occurs_rec(ctx, hole_id, val, depth + 1)
            || occurs_opt_rec(ctx, hole_id, default, depth + 1)
          })
          || occurs_opt_rec(ctx, hole_id, tail, depth + 1)
        v.Neut(v.NVar(_)) -> False
        v.Neut(v.NHole(_, None)) -> False
        v.Neut(v.NHole(_, Some(id))) -> id == hole_id
        v.Neut(v.NApp(fun_neut, arg_val)) ->
          occurs_rec(ctx, hole_id, v.Neut(fun_neut), depth + 1)
          || occurs_rec(ctx, hole_id, arg_val, depth + 1)
        v.Neut(v.NMatch(env, arg, cases)) ->
          occurs_rec(ctx, hole_id, arg, depth + 1)
          || list.any(cases, occurs_case(ctx, env, hole_id, depth + 1, _))
        v.Neut(v.NCall(_, ret, arg)) ->
          occurs_rec(ctx, hole_id, ret, depth + 1)
          || occurs_rec(ctx, hole_id, arg, depth + 1)
        v.For(env, #(_, param), body) -> {
          let env = v.env_push(env, 1)
          occurs_rec(ctx, hole_id, param, depth + 1)
          || occurs_term_rec(ctx, env, hole_id, body, depth + 1)
        }
        v.Lam(env, #(_, param), body) -> {
          let env = v.env_push(env, 1)
          occurs_rec(ctx, hole_id, param, depth + 1)
          || occurs_term_rec(ctx, env, hole_id, body, depth + 1)
        }
        v.Pi(env, #(_, domain), codomain) -> {
          let env = v.env_push(env, 1)
          occurs_rec(ctx, hole_id, domain, depth + 1)
          || occurs_term_rec(ctx, env, hole_id, codomain, depth + 1)
        }
        v.Fix(env, _, body) -> {
          let env = v.env_push(env, 1)
          occurs_term_rec(ctx, env, hole_id, body, depth + 1)
        }
        // Type definitions: the parameter types live in the definition's
        // frame; the argument and variant terms are evaluated with the
        // parameters as fresh (rigid) bindings, like `For` bodies.
        v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> {
          let p_env = v.env_push(env, list.length(params))
          list.any(params, fn(param) {
            let #(_, typ) = param
            occurs_rec(ctx, hole_id, typ, depth + 1)
          })
          || occurs_term_rec(ctx, p_env, hole_id, arg, depth + 1)
          || list.any(variants, fn(variant) {
            let #(_, v.Variant(vparams, varg, vret)) = variant
            let vp_env = v.env_push(p_env, list.length(vparams))
            list.any(vparams, fn(param) {
              let #(_, typ) = param
              occurs_rec(ctx, hole_id, typ, depth + 1)
            })
            || occurs_term_rec(ctx, vp_env, hole_id, varg, depth + 1)
            || occurs_term_rec(ctx, vp_env, hole_id, vret, depth + 1)
          })
        }
        v.Err -> False
      }
    }
  }
}

/// `occurs` for an optional value (record defaults, tails).
pub fn occurs_opt(
  ctx: Context,
  hole_id: Int,
  opt_value: Option(Value),
) -> Bool {
  case opt_value {
    Some(value) -> occurs(ctx, hole_id, value)
    None -> False
  }
}

fn occurs_opt_rec(
  ctx: Context,
  hole_id: Int,
  opt_value: Option(Value),
  depth: Int,
) -> Bool {
  case opt_value {
    Some(value) -> occurs_rec(ctx, hole_id, value, depth)
    None -> False
  }
}

/// `occurs` inside a value body: the term is evaluated first so that
/// variables and holes in the body are seen as values.
pub fn occurs_term(ctx: Context, env: Env, hole_id: Int, term: Term) -> Bool {
  let value = eval(ctx.ffi, env, term)
  occurs(ctx, hole_id, value)
}

fn occurs_term_rec(
  ctx: Context,
  env: Env,
  hole_id: Int,
  term: Term,
  depth: Int,
) -> Bool {
  let value = eval(ctx.ffi, env, term)
  occurs_rec(ctx, hole_id, value, depth)
}

fn occurs_case(ctx: Context, env: Env, hole_id: Int, depth: Int, c: Case) -> Bool {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  case c.guard {
    None -> occurs_term_rec(ctx, env, hole_id, c.body, depth + 1)
    Some(#(g_term, g_pattern)) -> {
      let g_vars = list.length(tm.bindings(g_pattern))
      occurs_term_rec(ctx, env, hole_id, g_term, depth + 1)
      || occurs_term_rec(ctx, v.env_push(env, g_vars), hole_id, c.body, depth + 1)
    }
  }
}
