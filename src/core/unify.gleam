/// Unification — Higher-order unification for Core values.
import core/context.{
  type Context, CallArityMismatch, Context, InfiniteType, NeutralTypeMismatch,
  RcdFieldsMismatch, TypeMismatch, TypeVariantUndefined, with_err,
}
import core/eval.{eval}
import core/occurs.{occurs}
import core/resolve.{resolve}
import core/term.{type Term}
import core/unwrap.{unwrap}
import core/value.{type Env, type Neut, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{type Span}

pub fn unify(ctx: Context, a: #(Value, Span), b: #(Value, Span)) -> Context {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case unwrap(ctx.ffi, ctx.subst, value1), unwrap(ctx.ffi, ctx.subst, value2) {
    // Try to solve holes before unifying any concrete values
    v.Neut(v.NHole(id1)), v.Neut(v.NHole(id2)) if id1 == id2 -> ctx
    _, v.Neut(v.NHole(id)) -> solve_hole(ctx, id, value1, s1)
    v.Neut(v.NHole(id)), _ -> solve_hole(ctx, id, value2, s2)
    v.Neut(n1), v.Neut(n2) -> unify_neut(ctx, #(n1, s1), #(n2, s2))
    // Unify concrete values
    v.Typ(u1), v.Typ(u2) if u1 == u2 -> ctx
    v.Lit(v1), v.Lit(v2) if v1 == v2 -> ctx
    v.LitT(v1), v.LitT(v2) if v1 == v2 -> ctx
    v.Ctr(t1, a1), v.Ctr(t2, a2) if t1 == t2 -> unify(ctx, #(a1, s1), #(a2, s2))
    v.Ctr(t1, a1), v.Ctr(t2, a2) ->
      case context.lookup_type_def(ctx, t1), context.lookup_type_def(ctx, t2) {
        _, Some(#(env, tdef)) ->
          unify_gadt(ctx, #(t1, a1, s1), #(env, tdef, t2, a2, s2))
        Some(#(env, tdef)), _ ->
          unify_gadt(ctx, #(t2, a2, s2), #(env, tdef, t1, a1, s1))
        None, None -> with_err(ctx, TypeMismatch(a, b))
      }
    v.Rcd(fields1), v.Rcd(fields2) ->
      unify_rcd(ctx, #(fields1, s1), #(fields2, s2))
    v.RcdT(fields1), v.RcdT(fields2) ->
      unify_rcd_type(ctx, #(fields1, s1), #(fields2, s2))
    v.Lam(env1, i1, #(_, a1), b1), v.Lam(env2, i2, #(_, a2), b2) -> {
      todo as "unify Lam"
    }
    v.Pi(env1, i1, #(_, a1), b1), v.Pi(env2, i2, #(_, a2), b2) -> {
      todo as "unify Pi"
    }
    v.TypeDef(env1, tdef1), v.TypeDef(env2, tdef2) -> {
      todo as "unify TypeDef"
    }
    v.Err, v.Err -> ctx
    _, _ -> with_err(ctx, TypeMismatch(a, b))
  }
}

fn unify_with_term(
  ctx: Context,
  a: #(Value, Span),
  b: #(Env, Term, Span),
) -> Context {
  let #(env, term, s) = b
  let term = resolve(ctx.subst, term)
  let value = eval(ctx.ffi, env, term)
  unify(ctx, a, #(value, s))
}

/// GADT constructor unification.
///
/// This function unifies a concrete constructor value (a) with a GADT
/// type constructor (b). It is asymmetric by design:
///   - `a`: the inferred/actual constructor (tag, arg, span)
///   - `b`: the expected GADT type definition (env, type_def, tag, arg, span)
///
/// Key insight: In the check/infer workflow, one side always comes from
/// `lookup_type_def` (the expected type's TypeDef), so we always have a
/// valid type definition to inspect variants from. This makes the
/// asymmetry safe — we never need to try both directions.
///
/// The algorithm:
///   1. Instantiate the type definition's parameters (create holes)
///   2. Unify the type's argument with its parameter term (binds params)
///   3. Look up the constructor's tag in the type's variants
///   4. Instantiate the matching variant's parameters
///   5. Unify the constructor's arg with the variant's arg (binds more)
///   6. Evaluate the variant's return type and unify with the type arg
///   7. Pop the bound variables from the environment
fn unify_gadt(
  ctx: Context,
  a: #(String, Value, Span),
  b: #(Env, TypeDefinition, String, Value, Span),
) -> Context {
  let #(ctr_tag, ctr_arg, s1) = a
  let #(env, tdef, type_tag, type_arg, s2) = b
  // Instantiate the type definition's parameters by pushing fresh holes.
  // This binds the type's type parameters to concrete values during
  // unification (e.g., {n: 1, a: Float} binds n=1, a=Float).
  let #(env, ctx) = instantiate(ctx, env, tdef.params)
  // Unify the expected type's argument with the type definition's parameter
  // term. This step resolves any remaining type variables and binds the
  // instantiated holes to concrete values.
  let ctx = unify_with_term(ctx, #(type_arg, s2), #(env, tdef.arg, s2))
  // Look up the constructor's tag in the type definition's variants.
  // Assumption: the constructor tag must be a valid variant of this type.
  // If not found, it's a type error — the constructor doesn't belong
  // to this type definition.
  let ctx = case list.key_find(tdef.variants, ctr_tag) {
    Error(Nil) ->
      with_err(ctx, TypeVariantUndefined(#(ctr_tag, s1), #(tdef.variants, s2)))
    Ok(variant) -> {
      // Instantiate the variant's own parameters (e.g., the `m` in Cons<m>).
      // These are separate from the type's params and need their own scope.
      let #(env, ctx) = instantiate(ctx, env, variant.params)
      // Unify the constructor's actual argument with the variant's argument
      // pattern. This binds the variant's parameters and any type variables
      // in the argument (e.g., x: a, xs: #Vec {n: m, a: a} binds x, m).
      let ctx = unify_with_term(ctx, #(ctr_arg, s1), #(env, variant.arg, s2))
      // Evaluate the variant's return type (which now has all params bound)
      // and unify it with the expected type constructor to verify consistency.
      let expected = v.Ctr(type_tag, type_arg)
      let ctx =
        unify_with_term(ctx, #(expected, s2), #(env, variant.return_type, s2))
      // Pop the variant's parameter scope before the type's params scope.
      context.pop_vars(ctx, list.length(variant.params))
    }
  }
  // Pop the type definition's parameter scope.
  // Order matters: pop in reverse order of instantiation (inner → outer).
  context.pop_vars(ctx, list.length(tdef.params))
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
  a: #(List(#(String, #(Value, Option(Value)))), Span),
  b: #(List(#(String, #(Value, Option(Value)))), Span),
) -> Context {
  let #(fields1, s1) = a
  let #(fields2, s2) = b
  let sorted_names = fn(kvs: List(#(String, #(Value, Option(Value))))) {
    list.map(kvs, fn(kv) { kv.0 })
    |> list.sort(by: string.compare)
  }
  let ctx = case sorted_names(fields1), sorted_names(fields2) {
    names1, names2 if names1 != names2 ->
      with_err(ctx, RcdFieldsMismatch(#(names1, s1), #(names2, s2)))
    _, _ -> ctx
  }
  unify_rcd_type_fields(ctx, #(fields1, s1), #(fields2, s2))
}

fn unify_rcd_type_fields(
  ctx: Context,
  a: #(List(#(String, #(Value, Option(Value)))), Span),
  b: #(List(#(String, #(Value, Option(Value)))), Span),
) -> Context {
  let #(fields1, s1) = a
  let #(fields2, s2) = b
  case fields1 {
    [] -> ctx
    [#(name, #(value1, maybe_default)), ..fields1] ->
      case list.key_find(fields2, name) {
        Error(Nil) -> ctx
        Ok(#(value2, maybe_default2)) -> {
          let ctx = unify(ctx, #(value1, s1), #(value2, s2))
          let ctx = case maybe_default, maybe_default2 {
            Some(default1), Some(default2) ->
              unify(ctx, #(default1, s1), #(default2, s2))
            _, _ -> ctx
          }
          unify_rcd_type_fields(ctx, #(fields1, s1), #(fields2, s2))
        }
      }
  }
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

fn instantiate(
  ctx: Context,
  env: Env,
  params: List(#(String, Value)),
) -> #(Env, Context) {
  let ctx = context.push_var_param_list(ctx, params)
  let vars = list.take(ctx.env, list.length(params))
  #(list.append(vars, env), ctx)
}
