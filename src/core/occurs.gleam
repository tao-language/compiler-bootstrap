import core/context.{type Context}
import core/eval.{eval}
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Value} as v
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
      || occurs_opt(ctx, hole_id, tail)
    v.Neut(v.NVar(_)) -> False
    v.Neut(v.NHole(_, None)) -> False
    v.Neut(v.NHole(_, Some(id))) -> id == hole_id
    v.Neut(v.NApp(fun_neut, arg_val)) ->
      occurs(ctx, hole_id, v.Neut(fun_neut)) || occurs(ctx, hole_id, arg_val)
    v.Neut(v.NMatch(env, arg_neut, cases)) ->
      occurs(ctx, hole_id, v.Neut(arg_neut))
      || list.any(cases, occurs_case(ctx, env, hole_id, _))
    v.Neut(v.NCall(_, arg)) -> occurs(ctx, hole_id, arg)
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
