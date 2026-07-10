import core/context.{type Context}
import core/eval.{eval}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Neut, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}

// TODO: replace ctx with only ffi, do not unwrap
pub fn occurs(ctx: Context, hole_id: Int, value: Value) -> Bool {
  case unwrap(ctx.ffi, ctx.subst, value) {
    v.Typ(_) -> False
    v.Lit(_) -> False
    v.LitT(_) -> False
    v.Ctr(_, arg) -> occurs(ctx, hole_id, arg)
    v.Rcd(fields, tail) ->
      list.any(fields, fn(field) {
        let #(_, #(val, default)) = field
        occurs(ctx, hole_id, val) || occurs_opt(ctx, hole_id, default)
      })
    v.Neut(neut) -> occurs_neut(ctx, hole_id, neut)
    v.For(env, #(_, param), body) -> {
      let env = v.env_push(env, 1)
      occurs(ctx, hole_id, param) || occurs_term(ctx, env, hole_id, body)
    }
    v.Lam(env, #(_, param), body) -> {
      let env = v.env_push(env, 1)
      occurs(ctx, hole_id, param) || occurs_term(ctx, env, hole_id, body)
    }
    v.Pi(env, #(_, domain), codomain) -> {
      let env = v.env_push(env, 1)
      occurs(ctx, hole_id, domain) || occurs_term(ctx, env, hole_id, codomain)
    }
    v.Fix(env, _, body) -> {
      let env = v.env_push(env, 1)
      occurs_term(ctx, env, hole_id, body)
    }
    v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> todo
    v.Err -> False
  }
}

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

pub fn occurs_term(ctx: Context, env: Env, hole_id: Int, term: Term) -> Bool {
  let value = eval(ctx.ffi, env, term)
  occurs(ctx, hole_id, value)
}

fn occurs_neut(ctx: Context, hole_id: Int, neut: Neut) -> Bool {
  case neut {
    v.NVar(_) -> False
    v.NHole(_, id) -> id == hole_id
    v.NApp(fun, arg) ->
      occurs_neut(ctx, hole_id, fun) || occurs(ctx, hole_id, arg)
    v.NMatch(env, arg, cases) ->
      occurs_neut(ctx, hole_id, arg)
      || list.any(cases, occurs_case(ctx, env, hole_id, _))
    v.NCall(_, returns, args) ->
      occurs(ctx, hole_id, returns) || list.any(args, occurs(ctx, hole_id, _))
  }
}

fn occurs_case(ctx: Context, env: Env, hole_id: Int, c: Case) -> Bool {
  let env = v.env_push(env, list.length(tm.bindings(c.pattern)))
  case c.guard {
    None -> occurs_term(ctx, env, hole_id, c.body)
    Some(#(g_term, g_pattern)) -> {
      let g_vars = list.length(tm.bindings(g_pattern))
      occurs_term(ctx, env, hole_id, g_term)
      || occurs_term(ctx, v.env_push(env, g_vars), hole_id, c.body)
    }
  }
}
