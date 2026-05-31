/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Error handling for mismatches
/// - Constructor tag and argument unification
import core/context.{
  Context, TypeMismatch, TypeVariantUndefined, new_ctx, with_err,
} as ctx
import core/term as tm
import core/unify.{unify}
import core/value as v
import gleeunit
import syntax/span

pub fn main() {
  gleeunit.main()
}

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

pub fn unify_vtyp_type_mismatch_test() {
  let a = v.Typ(0)
  let b = v.Typ(1)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(b, s2), #(a, s1)))
}

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

pub fn unify_vlit_type_mismatch_test() {
  let a = v.int(1)
  let b = v.int(2)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(b, s2), #(a, s1)))
}

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

pub fn unify_litt_type_mismatch_test() {
  let a = v.int_t
  let b = v.float_t
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(b, s2), #(a, s1)))
}

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

pub fn unify_ctr_tag_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("B", v.int_t)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(b, s2), #(a, s1)))
}

pub fn unify_ctr_arg_mismatch_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("A", v.float_t)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(v.int_t, s1), #(v.float_t, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(v.float_t, s2), #(v.int_t, s1)))
}

// ============================================================================
// GADT unification
// ============================================================================

pub fn unify_ctr_gadt_undefined_type_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("T", v.float_t)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeMismatch(#(b, s2), #(a, s1)))
}

pub fn unify_ctr_gadt_undefined_variant_test() {
  let a = v.Ctr("A", v.int_t)
  let b = v.Ctr("T", v.float_t)
  let tdef = v.TypeDef([], [], [])
  let ctx0 = ctx.push_var(new_ctx, #("T", tdef, v.Typ(0)))
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeVariantUndefined(#("A", s1), #([], s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeVariantUndefined(#("A", s1), #([], s2)))
}

pub fn unify_ctr_gadt_bool_test() {
  let bool = v.ctr("Bool", [])
  let true_ = v.ctr("True", [])
  let false_ = v.ctr("False", [])
  // let Bool = $type {
  // | #True {} -> #Bool {}
  // | #False {} -> #Bool {}
  // }
  let tdef =
    v.TypeDef([], [], [
      #("True", #([], tm.Rcd([]), tm.ctr("Bool", []))),
      #("False", #([], tm.Rcd([]), tm.ctr("Bool", []))),
    ])
  let ctx0 = ctx.push_var(new_ctx, #("Bool", tdef, v.Typ(0)))
  // Check True constructor
  assert unify(ctx0, #(bool, s1), #(true_, s2)) == ctx0
  assert unify(ctx0, #(true_, s2), #(bool, s1)) == ctx0
  // Check False constructor
  assert unify(ctx0, #(bool, s1), #(false_, s2)) == ctx0
  assert unify(ctx0, #(false_, s2), #(bool, s1)) == ctx0
}

pub fn unify_ctr_gadt_option_test() {
  let option = fn(a) { v.Ctr("Option", a) }
  let none = v.ctr("None", [])
  let some = fn(x) { v.Ctr("Some", x) }
  // let Option = $type<a: $Type> {
  // | #None {} -> #Option #0  // a is #0
  // | #Some #0 -> #Option #0  // a is #0
  // }
  let tdef =
    v.TypeDef([], [#("a", v.Typ(0))], [
      #("None", #([], tm.Rcd([]), tm.Ctr("Option", tm.Var(0)))),
      #("Some", #([], tm.Var(0), tm.Ctr("Option", tm.Var(0)))),
    ])
  let ctx0 = ctx.push_var(new_ctx, #("Option", tdef, v.Typ(0)))
  // Check None constructor
  assert unify(ctx0, #(option(v.int_t), s1), #(none, s2))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  assert unify(ctx0, #(none, s2), #(option(v.int_t), s1))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  // Check Some constructor
  assert unify(ctx0, #(option(v.int_t), s1), #(some(v.int_t), s2))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  assert unify(ctx0, #(some(v.int_t), s2), #(option(v.int_t), s1))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  // Errors
  // TODO: save spans in ctx.types for better error reporting
  assert unify(ctx0, #(option(v.int_t), s1), #(some(v.float_t), s2))
    == Context(
      ..ctx0,
      subst: [#(0, v.float_t)],
      errors: [TypeMismatch(#(v.int_t, s1), #(v.float_t, s1))],
      hole_counter: 1,
    )
}

pub fn unify_ctr_gadt_vec_test() {
  let vec = fn(n, a) { v.ctr("Vec", [#("n", n), #("a", a)]) }
  let nil = v.ctr("Nil", [])
  let cons = fn(x, xs) { v.ctr("Cons", [#("x", x), #("xs", xs)]) }
  // let Vec = $type<n: $Int, a: $Type> {
  // | #Nil        {}                            -> #Vec {n: 0,     a: a}  // n is #1, a is #0
  // | #Cons<m: ?> {x: a, xs: #Vec {n: m, a: a}} -> #Vec {n: m + 1, a: a}  // n is #2, a is #1, m is #0
  // }
  let a = tm.Var(0)
  let nil_ret = tm.ctr("Vec", [#("n", tm.int(0)), #("a", a)])
  let #(a, m) = #(tm.Var(1), tm.Var(0))
  let cons_arg = tm.Rcd([#("n", m), #("a", a)])
  let cons_ret =
    tm.ctr("Vec", [#("n", tm.Call("+", [m, tm.int(1)])), #("a", a)])
  let tdef =
    v.TypeDef([], [#("n", v.int_t), #("a", v.Typ(0))], [
      #("Nil", #([], tm.Rcd([]), nil_ret)),
      #("Cons", #([], cons_arg, cons_ret)),
    ])
  let ctx0 = ctx.push_var(new_ctx, #("Vec", tdef, v.Typ(0)))
  // Check Nil constructor
  let a = vec(v.int(0), v.float_t)
  let b = nil
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, subst: [#(1, v.float_t)], hole_counter: 2)
  assert unify(ctx0, #(b, s2), #(a, s1))
    == Context(..ctx0, subst: [#(1, v.float_t)], hole_counter: 2)
  // Check Cons constructor
  let a = vec(v.int(1), v.float_t)
  let b = cons(v.float_t, nil)
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, subst: [#(1, v.float_t)], hole_counter: 2)
  assert unify(ctx0, #(b, s2), #(a, s1))
    == Context(..ctx0, subst: [#(1, v.float_t)], hole_counter: 2)
  // Check nested Cons constructors
}

// ============================================================================
// Record unification
// ============================================================================

pub fn unify_rcd_empty_test() {
  todo
}

pub fn unify_rcd_fields_mismatch_test() {
  todo
}

pub fn unify_rcd_different_order_test() {
  todo
}

// ============================================================================
// Record type unification
// ============================================================================

pub fn unify_rcdt_empty_test() {
  todo
}

pub fn unify_rcdt_fields_mismatch_test() {
  todo
}

pub fn unify_rcdt_different_order_test() {
  todo
}

// ============================================================================
// Neutral variable unification
// ============================================================================

pub fn unify_neut_nvar_same_test() {
  todo
}

pub fn unify_neut_nvar_different_test() {
  todo
}

// ============================================================================
// Neutral hole unification
// ============================================================================

pub fn unify_neut_nhole_same_test() {
  todo
}

pub fn unify_neut_nhole_solve_test() {
  todo
}

pub fn unify_neut_nhole_infinite_type_test() {
  todo
}

// ============================================================================
// Neutral application unification
// ============================================================================

pub fn unify_neut_napp_test() {
  todo
}

// ============================================================================
// Neutral match unification
// ============================================================================

pub fn unify_neut_nmatch_empty_cases_test() {
  todo
}

pub fn unify_neut_nmatch_case_without_bindings_test() {
  todo
}

pub fn unify_neut_nmatch_case_with_bindings_test() {
  todo
}

// ============================================================================
// Neutral call unification
// ============================================================================

pub fn unify_neut_ncall_empty_args_test() {
  todo
}

pub fn unify_neut_ncall_name_mismatch_test() {
  todo
}

// ============================================================================
// Lambda unification
// ============================================================================

pub fn unify_lam_identity_test() {
  todo
}

pub fn unify_lam_different_env_closure_test() {
  todo
}

// ============================================================================
// Pi type unification
// ============================================================================

pub fn unify_pi_identity_test() {
  todo
}

pub fn unify_pi_different_env_closure_test() {
  todo
}

// ============================================================================
// Fix-point unification
// ============================================================================

pub fn unify_fix_test() {
  todo
}

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
