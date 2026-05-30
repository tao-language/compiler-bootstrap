/// Unification — Higher-order unification for Core values.
import core/context.{type Context, TypeMismatch}
import core/value.{type Neut, type Value} as v
import syntax/span.{type Span}

pub fn unify(ctx: Context, a: #(Value, Span), b: #(Value, Span)) -> Context {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case value1, value2 {
    v.Typ(u1), v.Typ(u2) if u1 == u2 -> ctx
    v.Lit(v1), v.Lit(v2) if v1 == v2 -> ctx
    v.LitT(v1), v.LitT(v2) if v1 == v2 -> ctx
    v.Ctr(t1, a1), v.Ctr(t2, a2) if t1 == t2 -> unify(ctx, #(a1, s1), #(a2, s2))
    v.Rcd(fields1), v.Rcd(fields2) ->
      // unify_rcd(state, fields1, fields2, s1)
      todo
    v.RcdT(fields1), v.RcdT(fields2) ->
      // unify_rcd_type(state, fields1, fields2, s1)
      todo
    v.Neut(n1), v.Neut(n2) -> unify_neut(ctx, #(n1, s1), #(n2, s2))
    v.Lam(i1, #(_, a1), #(env1, b1)), v.Lam(i2, #(_, a2), #(env2, b2)) -> {
      todo
    }
    v.Pi(i1, #(_, a1), #(env1, b1)), v.Pi(i2, #(_, a2), #(env2, b2)) -> {
      todo
    }
    v.Union(vars1), v.Union(vars2) -> {
      todo
    }
    v.Err, v.Err -> ctx
    _, _ -> context.with_err(ctx, TypeMismatch(a, b))
  }
}

fn unify_rcd(ctx: Context, a: #(List(#(String, Value)))) {
  todo
}

fn unify_neut(ctx: Context, a: #(Neut, Span), b: #(Neut, Span)) -> Context {
  todo
}
