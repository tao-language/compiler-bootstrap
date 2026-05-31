/// Unification — Higher-order unification for Core values.
import core/context.{
  type Context, CallArityMismatch, Context, InfiniteType, NeutralTypeMismatch,
  RcdFieldsMismatch, TypeMismatch, TypeVariantUndefined, with_err,
}
import core/eval.{eval}
import core/occurs.{occurs}
import core/term.{type Term}
import core/utils
import core/value.{type Env, type Neut, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{type Span}

pub fn unify(ctx: Context, a: #(Value, Span), b: #(Value, Span)) -> Context {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case value1, value2 {
    v.Typ(u1), v.Typ(u2) if u1 == u2 -> ctx
    v.Lit(v1), v.Lit(v2) if v1 == v2 -> ctx
    v.LitT(v1), v.LitT(v2) if v1 == v2 -> ctx
    v.Ctr(t1, a1), v.Ctr(t2, a2) if t1 == t2 -> unify(ctx, #(a1, s1), #(a2, s2))
    v.Ctr(t1, a1), v.Ctr(t2, a2) ->
      case context.lookup_type_def(ctx, t1), context.lookup_type_def(ctx, t2) {
        _, Some(tdef) -> unify_gadt(ctx, #(t1, a1, s1), #(value2, tdef, s2))
        Some(tdef), _ -> unify_gadt(ctx, #(t2, a2, s2), #(value1, tdef, s1))
        None, None -> with_err(ctx, TypeMismatch(a, b))
      }
    v.Rcd(fields1), v.Rcd(fields2) ->
      unify_rcd(ctx, #(fields1, s1), #(fields2, s2))
    v.RcdT(fields1), v.RcdT(fields2) ->
      unify_rcd_type(ctx, #(fields1, s1), #(fields2, s2))
    v.Neut(v.NHole(id1)), v.Neut(v.NHole(id2)) if id1 == id2 -> ctx
    _, v.Neut(v.NHole(id)) -> solve_hole(ctx, id, value1, s1)
    v.Neut(v.NHole(id)), _ -> solve_hole(ctx, id, value2, s2)
    v.Neut(n1), v.Neut(n2) -> unify_neut(ctx, #(n1, s1), #(n2, s2))
    v.Lam(env1, i1, #(_, a1), b1), v.Lam(env2, i2, #(_, a2), b2) -> {
      todo as "unify Lam"
    }
    v.Pi(env1, i1, #(_, a1), b1), v.Pi(env2, i2, #(_, a2), b2) -> {
      todo as "unify Pi"
    }
    v.TypeDef(env1, params1, variants1), v.TypeDef(env2, params2, variants2) -> {
      todo as "unify TypeDef"
    }
    v.Err, v.Err -> ctx
    _, _ -> with_err(ctx, TypeMismatch(a, b))
  }
}

fn unify_gadt(
  ctx: Context,
  a: #(String, Value, Span),
  b: #(Value, TypeDefinition, Span),
) -> Context {
  let #(ctr_tag, ctr_arg, s1) = a
  let #(expected, type_def, s2) = b
  let #(env, type_params, variants) = type_def
  case list.key_find(variants, ctr_tag) {
    Error(Nil) ->
      with_err(ctx, TypeVariantUndefined(#(ctr_tag, s1), #(variants, s2)))
    Ok(#(bindings, def_arg, ret_type)) -> {
      let params = list.reverse(list.append(type_params, bindings))
      let ctx = context.push_var_param_list(ctx, params)
      let vars = list.take(ctx.env, list.length(params))
      let env = list.append(vars, env)
      let def_arg_val = eval(ctx.ffi, env, def_arg)
      let ctx = unify(ctx, #(ctr_arg, s1), #(def_arg_val, s2))
      let ret_type_val = eval(ctx.ffi, env, ret_type)
      let ctx = unify(ctx, #(ret_type_val, s2), #(expected, s2))
      context.pop_vars(ctx, list.length(params))
    }
  }
}

fn unify_rcd(
  ctx: Context,
  a: #(List(#(String, Value)), Span),
  b: #(List(#(String, Value)), Span),
) -> Context {
  let #(fields1, s1) = a
  let #(fields2, s2) = b
  let sorted_names = fn(kvs: List(#(String, Value))) {
    list.map(kvs, fn(kv) { kv.0 })
    |> list.sort(by: string.compare)
  }
  let ctx = case sorted_names(fields1), sorted_names(fields2) {
    names1, names2 if names1 != names2 ->
      with_err(ctx, RcdFieldsMismatch(#(names1, s1), #(names2, s2)))
    _, _ -> ctx
  }
  unify_rcd_fields(ctx, #(fields1, s1), #(fields2, s2))
}

fn unify_rcd_fields(
  ctx: Context,
  a: #(List(#(String, Value)), Span),
  b: #(List(#(String, Value)), Span),
) -> Context {
  let #(fields1, s1) = a
  let #(fields2, s2) = b
  case fields1 {
    [] -> ctx
    [#(name, value1), ..fields1] ->
      case list.key_find(fields2, name) {
        Error(Nil) -> ctx
        Ok(value2) -> {
          let ctx = unify(ctx, #(value1, s1), #(value2, s2))
          unify_rcd_fields(ctx, #(fields1, s1), #(fields2, s2))
        }
      }
  }
}

fn unify_rcd_type(
  ctx: Context,
  a: #(List(#(String, Value, Option(Value))), Span),
  b: #(List(#(String, Value, Option(Value))), Span),
) -> Context {
  todo as "unify RcdT"
}

fn unify_neut(ctx: Context, a: #(Neut, Span), b: #(Neut, Span)) -> Context {
  let #(n1, s1) = a
  let #(n2, s2) = b
  case n1, n2 {
    v.NVar(lv1), v.NVar(lv2) if lv1 == lv2 -> ctx
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
  case hole_id >= 0 {
    True ->
      // Concrete hole, do occurs check and solve with a substitution
      case occurs(ctx, hole_id, value) {
        True -> with_err(ctx, InfiniteType(hole_id, value, span))
        False ->
          case list.key_find(ctx.subst, hole_id) {
            Error(Nil) ->
              Context(..ctx, subst: [#(hole_id, value), ..ctx.subst])
            Ok(existing) ->
              // TODO: save spans in ctx.types for better error reporting
              unify(ctx, #(value, span), #(existing, span))
          }
      }
    False -> {
      // Unknown hole, instantiate a fresh new hole.
      let #(hole_id, ctx) = context.new_hole(ctx)
      solve_hole(ctx, hole_id, value, span)
    }
  }
}
