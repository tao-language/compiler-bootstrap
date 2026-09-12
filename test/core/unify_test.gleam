/// Tests for the `unify` module — higher-order unification for Core values.
import core/context.{Context, new_ctx}
import core/error as e
import core/literals as lit
import core/occurs
import core/term as tm
import core/unify.{unify}
import core/value as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span

const s1 = span.Span("", 1, 1, 1, 1)

const s2 = span.Span("", 2, 2, 2, 2)

// ============================================================================
// Typ (universe level) unification
// ============================================================================

pub fn unify_vtyp_same_universe_test() {
  let a = v.Typ(0)
  let b = v.Typ(0)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
  assert unify(ctx0, #(b, s2), #(a, s1)) == ctx0
}

// pub fn unify_vtyp_type_mismatch_test() {
//   let a = v.Typ(0)
//   let b = v.Typ(1)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(b, s2), #(a, s1)))
// }

// ============================================================================
// Literal value unification
// ============================================================================

pub fn unify_vlit_same_int_test() {
  let a = v.int(42)
  let b = v.int(42)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
  assert unify(ctx0, #(b, s2), #(a, s1)) == ctx0
}

// pub fn unify_vlit_type_mismatch_test() {
//   let a = v.int(1)
//   let b = v.int(2)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(b, s2), #(a, s1)))
// }

// ============================================================================
// Literal type unification
// ============================================================================

pub fn unify_litt_same_test() {
  let a = v.int_t
  let b = v.int_t
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
  assert unify(ctx0, #(b, s2), #(a, s1)) == ctx0
}

// pub fn unify_litt_type_mismatch_test() {
//   let a = v.int_t
//   let b = v.float_t
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(b, s2), #(a, s1)))
// }

// ============================================================================
// Constructor unification
// ============================================================================

pub fn unify_ctr_same_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.int_t)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
  assert unify(ctx0, #(b, s2), #(a, s1)) == ctx0
}

// pub fn unify_ctr_tag_mismatch_test() {
//   let a = v.Ctr("A", v.int_t)
//   let b = v.Ctr("B", v.int_t)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(b, s2), #(a, s1)))
// }

// pub fn unify_ctr_arg_mismatch_test() {
//   let a = v.Ctr("A", v.int_t)
//   let b = v.Ctr("A", v.float_t)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int_t, s1), #(v.float_t, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(v.float_t, s2), #(v.int_t, s1)))
// }

// ============================================================================
// GADT unification
// ============================================================================

// pub fn unify_ctr_gadt_undefined_type_test() {
//   let a = v.Ctr("A", v.int_t)
//   let b = v.Ctr("T", v.float_t)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
//   assert unify(ctx0, #(b, s2), #(a, s1))
//     == with_err(ctx0, e.TypeMismatch(#(b, s2), #(a, s1)))
// }

// pub fn unify_ctr_gadt_undefined_variant_test() {
//   let a = v.Ctr("A", v.int_t)
//   let b = v.Ctr("T", v.float_t)
//   let tdef = v.TypeDefinition([], tm.Rcd([], None), [])
//   let ctx0 =
//     context.push_var(new_ctx, #("T", Some(v.TypeDef([], tdef)), Some(v.Typ(0))))
//   let ctx = unify(ctx0, #(a, s1), #(b, s2))
//   assert ctx.errors
//     == [
//       e.TypeMismatch(#(v.float_t, s2), #(v.rcd([]), s2)),
//       e.TypeVariantUndefined(#("A", s1), #([], s2)),
//     ]
// }

pub fn unify_ctr_gadt_bool_test() {
  let bool = v.ctr("Bool", [])
  let true_ = v.ctr("True", [])
  let false_ = v.ctr("False", [])
  // let Bool = $type {} {
  // | #True {} -> #Bool {}
  // | #False {} -> #Bool {}
  // }
  let tdef =
    v.TypeDefinition(params: [], arg: tm.rcd([]), variants: [
      #("True", v.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
      #("False", v.Variant([], tm.rcd([]), tm.ctr("Bool", []))),
    ])
  let ctx0 =
    context.push_var_opt(new_ctx, #(
      "Bool",
      Some(v.TypeDef([], tdef)),
      Some(v.Typ(0)),
    ))
  // Check: True constructor
  assert unify(ctx0, #(bool, s1), #(true_, s2)) == ctx0
  assert unify(ctx0, #(true_, s2), #(bool, s1)) == ctx0
  // Check: False constructor
  assert unify(ctx0, #(bool, s1), #(false_, s2)) == ctx0
  assert unify(ctx0, #(false_, s2), #(bool, s1)) == ctx0
}

pub fn unify_ctr_gadt_option_test() {
  let option = fn(a) { v.Ctr("Option", a) }
  let none = v.ctr("None", [])
  let some = fn(x) { v.Ctr("Some", x) }
  // let Option = $type<a: $Type> a {
  // | #None {} -> #Option #0  // a is #0
  // | #Some #0 -> #Option #0  // a is #0
  // }
  let tdef =
    v.TypeDefinition(params: [#("a", v.Typ(0))], arg: tm.Var(0), variants: [
      #("None", v.Variant([], tm.rcd([]), tm.Ctr("Option", tm.Var(0)))),
      #("Some", v.Variant([], tm.Var(0), tm.Ctr("Option", tm.Var(0)))),
    ])
  let ctx0 =
    context.push_var_opt(new_ctx, #(
      "Option",
      Some(v.TypeDef([], tdef)),
      Some(v.Typ(0)),
    ))
  // Check: None constructor. The stored env is the frame current when the
  // hole was solved — the type-parameter scope is still on the stack at that
  // point (`unify_gadt` pops it only after the arg/return unifications). The
  // fresh parameter value (hole 0, the very hole being solved) is innermost,
  // ahead of `ctx0`'s module record entry.
  let option_env = case ctx0.env {
    [module_entry, ..] -> [
      v.Neut(v.NHole([v.TypeDef([], tdef)], Some(0))),
      module_entry,
    ]
    _ -> panic as "unexpected ctx0.env"
  }
  let ctx = unify(ctx0, #(option(v.int_t), s1), #(none, s2))
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.subst == [#(0, #(option_env, v.int_t))]
  assert ctx.hole_counter == 1
  let ctx = unify(ctx0, #(none, s2), #(option(v.int_t), s1))
  assert ctx.subst == [#(0, #(option_env, v.int_t))]
  assert ctx.hole_counter == 1
  // Check: Some constructor
  let ctx = unify(ctx0, #(option(v.int_t), s1), #(some(v.int_t), s2))
  assert ctx.subst == [#(0, #(option_env, v.int_t))]
  assert ctx.hole_counter == 1
  let ctx = unify(ctx0, #(some(v.int_t), s2), #(option(v.int_t), s1))
  assert ctx.subst == [#(0, #(option_env, v.int_t))]
  assert ctx.hole_counter == 1
  // Error: type mismatch
  // TODO: save spans in ctx.types for better error reporting
  let ctx = unify(ctx0, #(option(v.int_t), s1), #(some(v.float_t), s2))
  // assert ctx.errors == [e.TypeMismatch(#(v.float_t, s2), #(v.int_t, s1))]
  assert list.length(ctx.errors) == 1
}

pub fn unify_ctr_gadt_vec_test() {
  let vec = fn(n, a) { v.ctr("Vec", [#("n", n), #("a", a)]) }
  let nil = v.ctr("Nil", [])
  let cons = fn(x, xs) { v.ctr("Cons", [#("x", x), #("xs", xs)]) }
  // let Vec = $type<n: $Int, a: $Type> {n: n, a: a} {
  // | #Nil        {}                            -> #Vec {n: 0,     a: a}  // n is #1, a is #0
  // | #Cons<m: ?> {x: a, xs: #Vec {n: m, a: a}} -> #Vec {n: m + 1, a: a}  // n is #2, a is #1, m is #0
  // }
  let a = tm.Var(0)
  let nil_ret = tm.ctr("Vec", [#("n", tm.int(0)), #("a", a)])
  let #(_n, a, m) = #(tm.Var(2), tm.Var(1), tm.Var(0))
  let cons_arg =
    tm.rcd([#("x", a), #("xs", tm.ctr("Vec", [#("n", m), #("a", a)]))])
  let cons_ret =
    tm.ctr("Vec", [
      #("n", tm.Call("+", tm.int_t, tm.rcd([#("", m), #("", tm.int(1))]))),
      #("a", a),
    ])
  let tdef =
    v.TypeDefinition(
      params: [#("n", v.int_t), #("a", v.Typ(0))],
      arg: tm.rcd([#("n", tm.Var(1)), #("a", tm.Var(0))]),
      variants: [
        #("Nil", v.Variant([], tm.rcd([]), nil_ret)),
        #(
          "Cons",
          v.Variant([#("m", v.hole_open([], None))], cons_arg, cons_ret),
        ),
      ],
    )
  let ctx0 =
    Context(
      ..context.push_var_opt(new_ctx, #(
        "Vec",
        Some(v.TypeDef([], tdef)),
        Some(v.Typ(0)),
      )),
      ffi: [
        #("+", fn(arg) {
          case arg {
            v.Rcd(
              [#(_, #(v.Lit(lit.Int(x)), _)), #(_, #(v.Lit(lit.Int(y)), _))],
              None,
            ) -> Some(v.int(x + y))
            _ -> None
          }
        }),
      ],
    )
  // Check: Nil constructor
  let a = vec(v.int(0), v.float_t)
  let b = nil
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  // Check: Cons constructor
  let a = vec(v.int(1), v.float_t)
  let b = cons(v.float_t, nil)
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.env == ctx0.env
  assert ctx.types == ctx0.types
  assert ctx.errors == []
  // Check: nested Cons constructors
  let a = vec(v.int(2), v.float_t)
  let b = cons(v.float_t, cons(v.float_t, nil))
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
  // Error: Nil as non-zero Vec
  // TODO: improve spans for error reporting
  let a = vec(v.int(1), v.float_t)
  let b = nil
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // assert ctx.errors == [e.TypeMismatch(#(v.int(1), s1), #(v.int(0), s1))]
  assert list.length(ctx.errors) == 1
  // Error: nested Cons with type mismatch
  let a = vec(v.int(2), v.float_t)
  let b = cons(v.int_t, cons(v.float_t, nil))
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // assert ctx.errors == [e.TypeMismatch(#(v.int_t, s2), #(v.float_t, s1))]
  assert list.length(ctx.errors) == 1
}

/// B2: GADT refinement through a *hole* type parameter is recorded in the
/// substitution. Unifying the `LitInt` constructor against `Expr(a)` with
/// `a` an unsolved hole solves `a := Int` (via the variant's return type
/// `Expr(Int)`), so a later conflicting constraint `a := Bool` is an
/// error. (With a *neutral* parameter the refinement is instead left in
/// the deferred queue and accepted at resolve time — the dependent case.)
pub fn unify_gadt_hole_refinement_test() {
  let bool_t = tm.ctr("Bool", [])
  let tdef =
    v.TypeDefinition(
      params: [#("a", v.Typ(0))],
      arg: tm.rcd([#("a", tm.Var(0))]),
      variants: [
        #(
          "LitInt",
          v.Variant(
            [],
            tm.rcd([#("x", tm.int_t)]),
            tm.ctr("Expr", [#("", tm.int_t)]),
          ),
        ),
        #(
          "LitBool",
          v.Variant(
            [],
            tm.rcd([#("x", bool_t)]),
            tm.ctr("Expr", [#("", bool_t)]),
          ),
        ),
      ],
    )
  let ctx0 =
    context.push_var_opt(new_ctx, #(
      "Expr",
      Some(v.TypeDef([], tdef)),
      Some(v.Typ(0)),
    ))
  // Check: LitInt(x: ?n) against Expr(?a) — the refinement ?a := Int is
  // recorded by the return-type check.
  let #(id_n, ctx1) = context.new_hole(ctx0)
  let #(id_a, ctx2) = context.new_hole(ctx1)
  let litint = v.ctr("LitInt", [#("x", v.hole([], id_n))])
  let expr = v.ctr("Expr", [#("a", v.hole([], id_a))])
  let ctx = unify(ctx2, #(litint, s1), #(expr, s2))
  assert ctx.errors == []
  // The stored env is the frame current when the hole was solved: the
  // refinement is recorded by the return-type unification, which runs with
  // the type parameter still on the stack (hole 2, the neutral `Expr(?a)` —
  // the hole being refined), innermost ahead of the base `ctx2` frame.
  let param_env = case ctx2.env {
    [module_entry, ..] -> [
      v.Neut(v.NHole([v.TypeDef([], tdef)], Some(2))),
      module_entry,
    ]
    _ -> panic as "unexpected ctx2.env"
  }
  assert list.key_find(ctx.subst, id_n) == Ok(#(param_env, v.int_t))
  assert list.key_find(ctx.subst, id_a) == Ok(#(param_env, v.int_t))
  // Error: forcing the refined parameter to Bool now conflicts.
  let ctx = unify(ctx, #(v.hole([], id_a), s1), #(v.ctr("Bool", []), s2))
  assert list.length(ctx.errors) == 1
}

// ============================================================================
// Record unification
// ============================================================================

pub fn unify_rcd_empty_test() {
  let a = v.rcd([])
  let b = v.rcd([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_field_not_found_a_test() {
  let a = v.rcd([])
  let b = v.rcd([#("y", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, errors: [
      e.Error(e.RcdFieldNotFound(#("y", s2)), s1, []),
    ])
}

pub fn unify_rcd_field_not_found_b_test() {
  let a = v.rcd([#("x", v.int_t)])
  let b = v.rcd([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, errors: [
      e.Error(e.RcdFieldNotFound(#("x", s1)), s2, []),
    ])
}

pub fn unify_rcd_different_order_test() {
  let a = v.rcd([#("b", v.int_t), #("a", v.float_t)])
  let b = v.rcd([#("a", v.float_t), #("b", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_nested_same_test() {
  let inner = v.rcd([#("x", v.int(42))])
  let a =
    v.rcd([
      #("name", v.int(1)),
      #("value", inner),
    ])
  let b =
    v.rcd([
      #("value", inner),
      #("name", v.int(1)),
    ])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// Neutral variable unification
// ============================================================================

pub fn unify_neut_nvar_same_test() {
  let a = v.Neut(v.NVar(0))
  let b = v.Neut(v.NVar(0))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_nvar_different_test() {
  let a = v.Neut(v.NVar(0))
  let b = v.Neut(v.NVar(1))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors != []
}

// ============================================================================
// Neutral hole unification
// ============================================================================

pub fn unify_neut_nhole_same_test() {
  let a = v.Neut(v.NHole([], Some(0)))
  let b = v.Neut(v.NHole([], Some(0)))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_nhole_solve_test() {
  let a = v.Neut(v.NHole([], Some(0)))
  let b = v.int_t
  let ctx0 = new_ctx
  // Hole is solved with a substitution; hole_counter is unchanged
  // since no new_hole was called during this unify.
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, subst: [#(0, #([], v.int_t))])
}

pub fn unify_neut_nhole_infinite_type_test() {
  // Unifying a neutral hole with a value containing the same hole
  // triggers the occurs check, producing an InfiniteType error.
  let a = v.Neut(v.NHole([], Some(0)))
  let b = v.Neut(v.NApp(v.NHole([], Some(0)), v.int_t))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  let error =
    e.Error(
      e.InfiniteType(0, v.Neut(v.NApp(v.NHole([], Some(0)), v.int_t))),
      s2,
      [],
    )
  assert ctx.errors == [error]
}

/// KNOWN GAP (pinned, not yet fixed): the occurs check walks the solution
/// *value* but not a neutral hole's *captured env*. A hole whose captured env
/// contains the hole id (while the solution value does not) is NOT flagged as
/// an infinite type. Such a cycle is only broken later, at unwrap/resolve
/// time, by the `seen` stacks (left as an unsolved hole), not rejected up
/// front.
pub fn occurs_check_misses_captured_env_test() {
  let ctx = new_ctx
  // The solution value is a plain neutral var (no hole inside); the hole id
  // would appear only in a captured env, which `occurs` does not walk.
  let solution = v.var(0)
  assert occurs.occurs(ctx, 0, solution) == False
}

pub fn unify_neut_nhole_solve_twice_test() {
  // Solving the same hole twice should merge substitutions
  let a = v.Neut(v.NHole([], Some(0)))
  let b = v.Neut(v.NHole([], Some(0)))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  // Same hole IDs unify directly without calling solve_hole
  assert ctx == ctx0
}

// ============================================================================
// Neutral application unification
// ============================================================================

pub fn unify_neut_napp_test() {
  let a = v.Neut(v.NApp(v.NVar(0), v.int(1)))
  let b = v.Neut(v.NApp(v.NVar(0), v.int(1)))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// Neutral match unification
// ============================================================================

pub fn unify_neut_nmatch_same_test() {
  // Literal patterns keep the matches stuck (a neutral scrutinee may
  // still resolve to the literal); `PAny` cases would reduce eagerly.
  let a = v.Neut(v.NMatch([], v.Neut(v.NVar(0)), [tm.Case(tm.pint(1), None, tm.int(1))]))
  let b = v.Neut(v.NMatch([], v.Neut(v.NVar(0)), [tm.Case(tm.pint(1), None, tm.int(1))]))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

/// Matches with different numbers of cases cannot be the same value:
/// a `TypeMismatch` is reported (this used to be a `todo` panic).
pub fn unify_neut_nmatch_case_count_mismatch_test() {
  // Literal patterns keep both matches stuck.
  let a = v.Neut(v.NMatch([], v.Neut(v.NVar(0)), [tm.Case(tm.pint(1), None, tm.int(1))]))
  let b =
    v.Neut(
      v.NMatch([], v.Neut(v.NVar(0)), [
        tm.Case(tm.pint(1), None, tm.int(1)),
        tm.Case(tm.pint(2), None, tm.int(2)),
      ]),
    )
  let ctx = unify(new_ctx, #(a, s1), #(b, s2))
  let is_mismatch = case ctx.errors {
    [err, ..] -> err.data == e.TypeMismatch(#(a, s1), #(b, s2))
    _ -> False
  }
  assert is_mismatch
  assert list.length(ctx.errors) == 1
}

/// Exactly one case carrying a guard means the cases cannot both hold,
/// so the matches cannot be the same value.
pub fn unify_neut_nmatch_guard_mismatch_test() {
  // Literal patterns keep both matches stuck.
  let a = v.Neut(v.NMatch([], v.Neut(v.NVar(0)), [tm.Case(tm.pint(1), None, tm.int(1))]))
  let b =
    v.Neut(
      v.NMatch([], v.Neut(v.NVar(0)), [
        tm.Case(tm.pint(1), Some(#(tm.int(1), tm.PAny)), tm.int(1)),
      ]),
    )
  let ctx = unify(new_ctx, #(a, s1), #(b, s2))
  let is_guard_mismatch = case ctx.errors {
    [err, ..] ->
      case err.data {
        e.MatchGuardMismatch(guard, _span) -> guard == tm.int(1)
        _ -> False
      }
    _ -> False
  }
  assert is_guard_mismatch
  assert list.length(ctx.errors) == 1
}

/// A neutral match vs a concrete value is undecided while the scrutinee
/// is unknown: no error now, the pair is queued in `ctx.deferred` and
/// re-decided as holes get solved (see `deferred_constraint_test`).
pub fn unify_neut_nmatch_vs_concrete_is_deferred_test() {
  // A literal pattern keeps the match stuck (a `PAny` case would
  // reduce eagerly to its body and unify would decide immediately).
  let a = v.Neut(v.NMatch([], v.Neut(v.NVar(0)), [tm.Case(tm.pint(1), None, tm.int(1))]))
  let b = v.int_t
  let ctx = unify(new_ctx, #(a, s1), #(b, s2))
  assert ctx.errors == []
  assert list.length(ctx.deferred) == 1
}

// ============================================================================
// Neutral call unification
// ============================================================================

pub fn unify_neut_ncall_empty_args_test() {
  let a = v.Neut(v.NCall("f", v.int_t, v.rcd([])))
  let b = v.Neut(v.NCall("f", v.int_t, v.rcd([])))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_ncall_same_test() {
  let a = v.Neut(v.NCall("f", v.int_t, v.rcd([])))
  let b = v.Neut(v.NCall("f", v.int_t, v.rcd([])))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_ncall_name_mismatch_test() {
  // These are different neutral calls, but could still give the same value.
  // We don't have enough information to give an error here.
  let a = v.Neut(v.NCall("f", v.int_t, v.rcd([])))
  let b = v.Neut(v.NCall("g", v.int_t, v.rcd([])))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == []
}

pub fn unify_neut_ncall_arg_mismatch_test() {
  let a =
    v.Neut(v.NCall("f", v.int_t, v.rcd([#("", v.int_t), #("", v.float_t)])))
  let b =
    v.Neut(v.NCall(
      "f",
      v.int_t,
      v.rcd([#("", v.int_t), #("", v.float_t), #("", v.i64)]),
    ))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors != []
}

// ============================================================================
// Lambda unification
// ============================================================================

pub fn unify_lam_identity_test() {
  // Names don't matter, only the DeBruijn indices.
  let a = v.Lam([], #("x", v.int_t), tm.Var(0))
  let b = v.Lam([], #("y", v.int_t), tm.Var(0))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_lam_closure_test() {
  let a = v.Lam([], #("x", v.int_t), tm.int(42))
  let b = v.Lam([v.int(42)], #("y", v.int_t), tm.Var(1))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// pub fn unify_lam_param_type_mismatch_test() {
//   let a = v.Lam([], #("x", v.int_t), tm.Var(0))
//   let b = v.Lam([], #("y", v.float_t), tm.Var(0))
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int_t, s1), #(v.float_t, s2)))
// }

// pub fn unify_lam_body_mismatch_test() {
//   let a = v.Lam([], #("x", v.int_t), tm.int(1))
//   let b = v.Lam([], #("y", v.int_t), tm.int(2))
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int(1), s1), #(v.int(2), s2)))
// }

// ============================================================================
// Pi type unification
// ============================================================================

pub fn unify_pi_identity_test() {
  // Names don't matter, only the DeBruijn indices.
  let a = v.Pi([], #("x", v.int_t), tm.Var(0))
  let b = v.Pi([], #("y", v.int_t), tm.Var(0))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_pi_closure_test() {
  let a = v.Pi([], #("x", v.int_t), tm.int(42))
  let b = v.Pi([v.int(42)], #("y", v.int_t), tm.Var(1))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// pub fn unify_pi_param_type_mismatch_test() {
//   let a = v.Pi([], #("x", v.int_t), tm.Var(0))
//   let b = v.Pi([], #("y", v.float_t), tm.Var(0))
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int_t, s1), #(v.float_t, s2)))
// }

// pub fn unify_pi_body_mismatch_test() {
//   let a = v.Pi([], #("x", v.int_t), tm.int(1))
//   let b = v.Pi([], #("y", v.int_t), tm.int(2))
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int(1), s1), #(v.int(2), s2)))
// }

// ============================================================================
// Fix-point unification
// ============================================================================

pub fn unify_fix_identity_test() {
  // Names don't matter, only the DeBruijn indices.
  let a = v.Fix([], "x", tm.Var(0))
  let b = v.Fix([], "y", tm.Var(0))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_fix_closure_test() {
  let a = v.Fix([], "x", tm.int(42))
  let b = v.Fix([v.int(42)], "y", tm.Var(1))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// pub fn unify_fix_body_mismatch_test() {
//   let a = v.Fix([], "x", tm.int(1))
//   let b = v.Fix([], "y", tm.int(2))
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(v.int(1), s1), #(v.int(2), s2)))
// }

// ============================================================================
// Type definition unification
// ============================================================================

// ============================================================================
// Error unification
// ============================================================================

pub fn unify_err_test() {
  let a = v.Err
  let b = v.Err
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx == ctx0
}
// pub fn unify_err_mismatch_test() {
//   let a = v.Err
//   let b = v.int(0)
//   let ctx0 = new_ctx
//   assert unify(ctx0, #(a, s1), #(b, s2))
//     == with_err(ctx0, e.TypeMismatch(#(a, s1), #(b, s2)))
// }
