import core/context.{type Context}
import core/eval.{eval}
import core/unwrap.{unwrap}
import core/value.{type Neut, type Value} as v
import gleam/list
import gleam/option.{None, Some}

pub fn occurs(ctx: Context, hole_id: Int, value: Value) -> Bool {
  case unwrap(ctx.ffi, ctx.subst, value) {
    v.Typ(_) -> False
    v.Lit(_) -> False
    v.LitT(_) -> False
    v.Ctr(_, arg) -> occurs(ctx, hole_id, arg)
    v.Rcd(fields) ->
      list.any(fields, fn(field) {
        let #(_, val) = field
        occurs(ctx, hole_id, val)
      })
    v.RcdT(fields) ->
      list.any(fields, fn(field) {
        let #(_, #(type_val, maybe_default_val)) = field
        occurs(ctx, hole_id, type_val)
        || case maybe_default_val {
          Some(default_val) -> occurs(ctx, hole_id, default_val)
          None -> False
        }
      })
    v.Neut(neut) -> occurs_neut(ctx, hole_id, neut)
    v.Lam(env, #(_, param), body) -> {
      let body_val = eval(ctx.ffi, [v.var(list.length(env)), ..env], body)
      occurs(ctx, hole_id, param) || occurs(ctx, hole_id, body_val)
    }
    v.Pi(env, _, #(_, domain), codomain) -> {
      let codomain_val =
        eval(ctx.ffi, [v.var(list.length(env)), ..env], codomain)
      occurs(ctx, hole_id, domain) || occurs(ctx, hole_id, codomain_val)
    }
    v.Fix(env, _, body) -> {
      let body_val = eval(ctx.ffi, [v.var(list.length(env)), ..env], body)
      occurs(ctx, hole_id, body_val)
    }
    v.TypeDef(env, v.TypeDefinition(params, arg, variants)) -> todo
    v.Err -> False
  }
}

fn occurs_neut(ctx: Context, hole_id: Int, neut: Neut) -> Bool {
  case neut {
    v.NVar(_) -> False
    v.NHole(id) -> id == hole_id
    v.NApp(fun, arg) ->
      occurs_neut(ctx, hole_id, fun) || occurs(ctx, hole_id, arg)
    v.NMatch(env, arg, cases) -> todo
    v.NCall(_, args) -> list.any(args, occurs(ctx, hole_id, _))
  }
}
