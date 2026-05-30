/// Unification — Higher-order unification for Core values.
import core/context.{
  type Context, CallArityMismatch, Context, InfiniteType, NeutralTypeMismatch,
  TypeMismatch, with_err,
}
import core/occurs.{occurs}
import core/value.{type Neut, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
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
      unify_rcd(ctx, #(fields1, s1), #(fields2, s2))
    v.RcdT(fields1), v.RcdT(fields2) ->
      unify_rcd_type(ctx, #(fields1, s1), #(fields2, s2))
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

fn unify_rcd(
  ctx: Context,
  a: #(List(#(String, Value)), Span),
  b: #(List(#(String, Value)), Span),
) -> Context {
  todo
}

fn unify_rcd_type(
  ctx: Context,
  a: #(List(#(String, Value, Option(Value))), Span),
  b: #(List(#(String, Value, Option(Value))), Span),
) -> Context {
  todo
}

fn unify_neut(ctx: Context, a: #(Neut, Span), b: #(Neut, Span)) -> Context {
  let #(n1, s1) = a
  let #(n2, s2) = b
  case n1, n2 {
    v.NVar(lv1), v.NVar(lv2) if lv1 == lv2 -> ctx
    v.NHole(id1), v.NHole(id2) if id1 == id2 -> ctx
    v.NHole(id), _ -> solve_hole(ctx, id, v.Neut(n2), s2)
    _, v.NHole(id) -> solve_hole(ctx, id, v.Neut(n1), s1)
    v.NApp(fun1, arg1), v.NApp(fun2, arg2) -> {
      let ctx = unify_neut(ctx, #(fun1, s1), #(fun2, s2))
      unify(ctx, #(arg1, s1), #(arg2, s2))
    }
    v.NCall(name1, args1), v.NCall(name2, args2) if name1 == name2 -> {
      let ctx = case list.length(args1), list.length(args2) {
        len1, len2 if len1 == len2 -> ctx
        len1, len2 -> with_err(ctx, CallArityMismatch(#(len1, s1), #(len2, s2)))
      }
      unify_args(ctx, #(args1, s1), #(args2, s2))
    }
    v.NMatch(env1, arg1, cases1), v.NMatch(env2, arg2, cases2) -> {
      let ctx = unify_neut(ctx, #(arg1, s1), #(arg2, s2))
      todo as "unify_neut NMatch cases, use env to evaluate with pattern bindings"
    }
    _, _ -> with_err(ctx, NeutralTypeMismatch(a, b))
  }
}

fn unify_args(
  ctx: Context,
  a: #(List(Value), Span),
  b: #(List(Value), Span),
) -> Context {
  let #(args1, s1) = a
  let #(args2, s2) = b
  case args1, args2 {
    [arg1, ..args1], [arg2, ..args2] -> {
      let ctx = unify(ctx, #(arg1, s1), #(arg2, s2))
      unify_args(ctx, #(args1, s1), #(args2, s2))
    }
    _, _ -> ctx
  }
}

fn solve_hole(ctx: Context, hole_id: Int, value: Value, span: Span) -> Context {
  case occurs(ctx, hole_id, value) {
    True -> with_err(ctx, InfiniteType(hole_id, value, span))
    False -> Context(..ctx, subst: [#(hole_id, value), ..ctx.subst])
  }
}
