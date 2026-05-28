/// Unification — Higher-order unification for Core values.
///
/// Unification checks whether two `Value`s are "the same" and records
/// any mismatches as errors in the `State`. It also resolves holes
/// (unbound metavariables) by binding them to their types.
///
/// ## How it works
///
/// `unify(state, expected, actual)` recursively compares the two values:
///
/// - **Holes** (`VNeut(HHole(id))`) — unbound metavariables. When the
///   expected type is a hole, we bind it to the actual type in state.
///   An occur-check prevents binding a hole to a value containing itself.
/// - **Variables** (`VNeut(HVar(level))`) — compared structurally.
/// - **Same constructors** — recursively unify their fields.
/// - **Mismatched constructors** — record a `TypeMismatch` error.
///
/// Before comparing, both values are force-normalized via `force_value`
/// to resolve any already-solved holes. This ensures we compare
/// canonical forms.
///
/// The type checker calls this function at every place where two types
/// must agree. All errors accumulate in state; no early returns.
import core/context.{type Context, TypeMismatch}
import core/value.{type Neut, type Value} as v
import syntax/span.{type Span}

pub fn unify(
  ctx: Context,
  a: #(Value, Span),
  b: #(Value, Span),
) -> #(Value, Context) {
  let #(value1, s1) = a
  let #(value2, s2) = b
  case value1, value2 {
    v.Typ(u1), v.Typ(u2) if u1 == u2 -> #(value1, ctx)
    v.Lit(v1), v.Lit(v2) if v1 == v2 -> #(value1, ctx)
    v.LitT(v1), v.LitT(v2) if v1 == v2 -> #(value1, ctx)
    v.Ctr(t1, a1), v.Ctr(t2, a2) if t1 == t2 -> {
      let #(arg, state) = unify(ctx, #(a1, s1), #(a2, s2))
      #(v.Ctr(t1, arg), state)
    }
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
    v.Err, v.Err -> #(value1, ctx)
    _, _ -> #(v.Err, context.with_err(ctx, TypeMismatch(a, b)))
  }
}

fn unify_neut(
  ctx: Context,
  a: #(Neut, Span),
  b: #(Neut, Span),
) -> #(Value, Context) {
  todo
}
