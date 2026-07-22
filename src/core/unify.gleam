/// Unification — Higher-order unification for Core values.
import core/context.{type Context, Context, with_err}
import core/error as e
import core/eval.{eval}
import core/occurs.{occurs}
import core/quote
import core/term.{type Case, type Term} as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Neut, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

pub fn unify(ctx: Context, a: #(Value, Span), b: #(Value, Span)) -> Context {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case unwrap(ctx.ffi, ctx.subst, value1), unwrap(ctx.ffi, ctx.subst, value2) {
    // Try to solve holes before unifying any concrete values
    v.Neut(v.NHole(_, id1)), v.Neut(v.NHole(_, id2)) if id1 == id2 -> ctx
    value1, v.Neut(v.NHole(env, id)) -> solve_hole(ctx, id, value1, s1)
    v.Neut(v.NHole(env, id)), value2 -> solve_hole(ctx, id, value2, s2)
    v.Neut(v.NVar(lv1)), v.Neut(v.NVar(lv2)) if lv1 == lv2 -> ctx
    v.Neut(v.NApp(fun1, arg1)), v.Neut(v.NApp(fun2, arg2)) -> {
      let ctx = unify(ctx, #(v.Neut(fun1), s1), #(v.Neut(fun2), s2))
      unify(ctx, #(arg1, s1), #(arg2, s2))
    }
    v.Neut(v.NCall(x, arg1)), v.Neut(v.NCall(y, arg2)) if x == y ->
      unify(ctx, #(arg1, s1), #(arg2, s2))
    v.Neut(v.NMatch(env1, arg1, cases1)), v.Neut(v.NMatch(env2, arg2, cases2))
    -> {
      let ctx = unify(ctx, #(v.Neut(arg1), s1), #(v.Neut(arg2), s2))
      let ctx = case list.length(cases1) == list.length(cases2) {
        True -> ctx
        False -> {
          echo cases1
          echo cases2
          echo #("arity mismatch", list.length(cases1), list.length(cases2))
          todo as "error: MatchCasesArityMismatch"
        }
      }
      unify_match_case_list(ctx, #(env1, cases1, s1), #(env2, cases2, s2))
    }
    v.Neut(_) as value1, v.Neut(_) as value2 ->
      with_err(ctx, e.TypeMismatch(#(value1, s1), #(value2, s2)), s1)
    // Try to unify neutrals with concrete values
    value1, v.Neut(neut) ->
      check_neut_with_concrete(ctx, #(value1, s1), #(neut, s2))
    v.Neut(neut), value2 ->
      check_neut_with_concrete(ctx, #(value2, s2), #(neut, s1))
    // Quantifier instantiation
    v.For(env, _, body), value2 -> {
      let #(id, ctx) = context.new_hole(ctx)
      let env = [v.hole(env, Some(id)), ..env]
      let value1 = eval(ctx.ffi, env, body)
      unify(ctx, #(value1, s1), #(value2, s2))
    }
    value1, v.For(env, _, body) -> {
      let #(id, ctx) = context.new_hole(ctx)
      let env = [v.hole(env, Some(id)), ..env]
      let value2 = eval(ctx.ffi, env, body)
      unify(ctx, #(value1, s1), #(value2, s2))
    }
    // Unify concrete values
    v.Typ(u1), v.Typ(u2) if u1 == u2 -> ctx
    v.Lit(v1), v.Lit(v2) if v1 == v2 -> ctx
    v.LitT(v1), v.LitT(v2) if v1 == v2 -> ctx
    v.Ctr(t1, a1), v.Ctr(t2, a2) if t1 == t2 -> unify(ctx, #(a1, s1), #(a2, s2))
    v.Ctr(t1, a1) as value1, v.Ctr(t2, a2) as value2 ->
      case context.lookup_type_def(ctx, t1), context.lookup_type_def(ctx, t2) {
        _, Some(#(env, tdef)) ->
          unify_gadt(ctx, #(t1, a1, s1), #(env, tdef, t2, a2, s2))
        Some(#(env, tdef)), _ ->
          unify_gadt(ctx, #(t2, a2, s2), #(env, tdef, t1, a1, s1))
        None, None ->
          with_err(ctx, e.TypeMismatch(#(value1, s1), #(value2, s2)), s1)
      }
    // Record types
    v.Rcd([], None), v.Typ(_) -> ctx
    v.Rcd([], Some(tail)), v.Typ(_) -> unify(ctx, #(tail, s1), #(value2, s2))
    v.Rcd([#(_, #(value1, _)), ..fields], opt_tail), v.Typ(_) as value2 -> {
      let ctx = unify(ctx, #(value1, s1), #(value2, s2))
      unify(ctx, #(v.Rcd(fields, opt_tail), s1), #(value2, s2))
    }
    v.Typ(_) as value1, v.Rcd(..) as value2 ->
      unify(ctx, #(value2, s2), #(value1, s1))
    // Record row polymorphism
    v.Rcd([], Some(tail1)), v.Rcd([], Some(tail2)) ->
      unify(ctx, #(tail1, s1), #(tail2, s2))
    v.Rcd([], _), v.Rcd([], _) -> ctx
    v.Rcd([], None) as rcd1, v.Rcd([#(name, _), ..fields2], None) -> {
      let ctx = with_err(ctx, e.RcdFieldNotFound(#(name, s2)), s1)
      unify(ctx, #(rcd1, s1), #(v.Rcd(fields2, None), s2))
    }
    v.Rcd([], Some(tail1)), value2 -> unify(ctx, #(tail1, s1), #(value2, s2))
    value1, v.Rcd([], Some(tail2)) -> unify(ctx, #(value1, s1), #(tail2, s2))
    v.Rcd([field, ..fields1], tail1) as rcd1, v.Rcd(fields2, tail2) as rcd2 -> {
      let #(rcd2, ctx) =
        unify_rcd_field(ctx, #(rcd1, field, s1), #(rcd2, fields2, tail2, s2))
      unify(ctx, #(v.Rcd(fields1, tail1), s1), #(rcd2, s2))
    }
    // Lambdas
    v.Lam(env1, #(_, a1), b1), v.Lam(env2, #(_, a2), b2) -> {
      let ctx = unify(ctx, #(a1, s1), #(a2, s2))
      let v1 = eval(ctx.ffi, v.env_push(env1, 1), b1)
      let v2 = eval(ctx.ffi, v.env_push(env2, 1), b2)
      unify(ctx, #(v1, s1), #(v2, s2))
    }
    // Pi types
    v.Pi(env1, #(_, a1), b1), v.Pi(env2, #(_, a2), b2) -> {
      let ctx = unify(ctx, #(a1, s1), #(a2, s2))
      let v1 = eval(ctx.ffi, v.env_push(env1, 1), b1)
      let v2 = eval(ctx.ffi, v.env_push(env2, 1), b2)
      unify(ctx, #(v1, s1), #(v2, s2))
    }
    // Recursive terms
    v.Fix(env1, _, b1), v.Fix(env2, _, b2) -> {
      let v1 = eval(ctx.ffi, v.env_push(env1, 1), b1)
      let v2 = eval(ctx.ffi, v.env_push(env2, 1), b2)
      unify(ctx, #(v1, s1), #(v2, s2))
    }
    // Type definitions
    v.TypeDef(env1, tdef1), v.TypeDef(env2, tdef2) -> {
      todo as "unify TypeDef"
    }
    v.Err, v.Err -> ctx
    // Anything else is an error
    value1, value2 ->
      with_err(ctx, e.TypeMismatch(#(value1, s1), #(value2, s2)), s1)
  }
}

fn unify_rcd_field(
  ctx: Context,
  a: #(Value, #(String, #(Value, Option(Value))), Span),
  b: #(Value, List(#(String, #(Value, Option(Value)))), Option(Value), Span),
) -> #(Value, Context) {
  let #(rcd1, #(name, #(val1, default1)), s1) = a
  let #(rcd2, fields2, opt_tail2, s2) = b
  case tm.pop_field(fields2, name) {
    Some(#(#(val2, default2), fields2)) -> {
      let ctx = unify(ctx, #(val1, s1), #(val2, s2))
      let ctx = case default1, default2 {
        Some(v1), Some(v2) -> unify(ctx, #(v1, s1), #(v2, s2))
        _, _ -> ctx
      }
      #(v.Rcd(fields2, opt_tail2), ctx)
    }
    None -> {
      let ctx = case opt_tail2 {
        Some(tail2) -> unify(ctx, #(rcd1, s1), #(tail2, s2))
        None -> with_err(ctx, e.RcdFieldNotFound(#(name, s1)), s2)
      }
      #(rcd2, ctx)
    }
  }
}

fn check_neut_with_concrete(
  ctx: Context,
  a: #(Value, Span),
  b: #(Neut, Span),
) -> Context {
  // TODO: switch (a, b)
  let #(value, s1) = a
  let #(neut, s2) = b
  case neut {
    v.NVar(_) -> ctx
    v.NHole(env, id) -> todo
    v.NApp(fun_neut, arg_val) -> todo
    v.NMatch(env, arg_val, cases) ->
      check_neut_with_concrete_cases(ctx, env, arg_val, a, #(cases, s2))
    v.NCall(_, _) -> ctx
  }
}

fn check_neut_with_concrete_cases(
  ctx: Context,
  env: Env,
  arg: Neut,
  a: #(Value, Span),
  b: #(List(Case), Span),
) -> Context {
  // TODO: switch (a, b)
  let #(cases, s2) = b
  case cases {
    [] -> ctx
    [c, ..cases] -> {
      let num_vars = list.length(tm.bindings(c.pattern))
      let num_vars = case c.guard {
        None -> num_vars
        Some(#(_, g_pattern)) -> num_vars + list.length(tm.bindings(g_pattern))
      }
      let env = v.env_push(env, num_vars)
      let body_val = eval(ctx.ffi, env, c.body)
      let ctx = unify(ctx, a, #(body_val, s2))
      check_neut_with_concrete_cases(ctx, env, arg, a, #(cases, s2))
    }
  }
}

fn unify_with_term(
  ctx: Context,
  a: #(Value, Span),
  b: #(Env, Term, Span),
) -> Context {
  let #(env, term, s) = b
  // let term = resolve(ctx.ffi, ctx.subst, list.length(ctx.env), term)
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
      with_err(
        ctx,
        e.TypeVariantUndefined(#(ctr_tag, s1), #(tdef.variants, s2)),
        s2,
      )
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

fn unify_match_case(
  ctx: Context,
  a: #(Env, Case, Span),
  b: #(Env, Case, Span),
) -> Context {
  let #(env1, tm.Case(pat1, opt_guard1, body1), s1) = a
  let #(env2, tm.Case(pat2, opt_guard2, body2), s2) = b
  let env1 = v.env_push(env1, list.length(tm.bindings(pat1)))
  let env2 = v.env_push(env2, list.length(tm.bindings(pat2)))
  let #(env1, env2, ctx) = case opt_guard1, opt_guard2 {
    None, None -> #(env1, env2, ctx)
    Some(#(guard1, expect1)), Some(#(guard2, expect2)) -> {
      let v1 = eval(ctx.ffi, env1, guard1)
      let v2 = eval(ctx.ffi, env2, guard2)
      let ctx = unify(ctx, #(v1, s1), #(v2, s2))
      let env1 = v.env_push(env1, list.length(tm.bindings(expect1)))
      let env2 = v.env_push(env2, list.length(tm.bindings(expect2)))
      #(env1, env2, ctx)
    }
    _, _ -> todo as "error: MatchCaseGuardMismatch"
  }
  let v1 = eval(ctx.ffi, env1, body1)
  let v2 = eval(ctx.ffi, env2, body2)
  unify(ctx, #(v1, s1), #(v2, s2))
}

fn unify_match_case_list(
  ctx: Context,
  a: #(Env, List(Case), Span),
  b: #(Env, List(Case), Span),
) -> Context {
  let #(env1, cases1, s1) = a
  let #(env2, cases2, s2) = b
  case cases1, cases2 {
    [c1, ..cases1], [c2, ..cases2] -> {
      let ctx = unify_match_case(ctx, #(env1, c1, s1), #(env2, c2, s2))
      unify_match_case_list(ctx, #(env1, cases1, s1), #(env2, cases2, s2))
    }
    _, _ -> ctx
  }
}

// TODO: save hole env into ctx.subst
fn solve_hole(
  ctx: Context,
  opt_id: Option(Int),
  value: Value,
  span: Span,
) -> Context {
  case opt_id {
    Some(id) ->
      // Concrete hole, do occurs check and solve with a substitution
      case occurs(ctx, id, value) {
        True -> with_err(ctx, e.InfiniteType(id, value), span)
        False ->
          case list.key_find(ctx.subst, id) {
            Error(Nil) -> Context(..ctx, subst: [#(id, value), ..ctx.subst])
            Ok(existing) ->
              // TODO: save spans in ctx.types for better error reporting
              // TODO: does the subst need to be replaced with the new value?
              unify(ctx, #(value, span), #(existing, span))
          }
      }
    None -> {
      // Unknown hole, instantiate a fresh new hole.
      let #(id, ctx) = context.new_hole(ctx)
      solve_hole(ctx, Some(id), value, span)
    }
  }
}

fn instantiate(
  ctx: Context,
  env: Env,
  params: List(#(String, Value)),
) -> #(Env, Context) {
  let ctx =
    list.map(params, fn(param) {
      let #(name, type_) = param
      #(name, None, Some(type_))
    })
    |> context.push_var_list(ctx, _)
  let vars = list.take(ctx.env, list.length(params))
  #(list.append(vars, env), ctx)
}
