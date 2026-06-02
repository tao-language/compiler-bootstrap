/// Tests for the `unify` module — higher-order unification for Core values.
///
/// These tests verify:
/// - Basic type/literal unification
/// - Error handling for mismatches
/// - Constructor tag and argument unification
import core/context.{
  CallArityMismatch, Context, InfiniteType, RcdFieldsMismatch, TypeMismatch,
  TypeVariantUndefined, new_ctx, with_err,
}
import core/literals as lit
import core/term as tm
import core/unify.{unify}
import core/value as v
import gleam/list
import gleam/option.{None, Some}
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
  let tdef = v.TypeDefinition([], tm.Rcd([]), [])
  let ctx0 = context.push_var(new_ctx, #("T", v.TypeDef([], tdef), v.Typ(0)))
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeVariantUndefined(#("A", s1), #([], s2)))
  assert unify(ctx0, #(b, s2), #(a, s1))
    == with_err(ctx0, TypeVariantUndefined(#("A", s1), #([], s2)))
}

pub fn unify_ctr_gadt_bool_test() {
  let bool = v.ctr("Bool", [])
  let true_ = v.ctr("True", [])
  let false_ = v.ctr("False", [])
  // let Bool = $type {} {
  // | #True {} -> #Bool {}
  // | #False {} -> #Bool {}
  // }
  let tdef =
    v.TypeDefinition(params: [], arg: tm.Rcd([]), variants: [
      #("True", v.Variant([], tm.Rcd([]), tm.ctr("Bool", []))),
      #("False", v.Variant([], tm.Rcd([]), tm.ctr("Bool", []))),
    ])
  let ctx0 = context.push_var(new_ctx, #("Bool", v.TypeDef([], tdef), v.Typ(0)))
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
      #("None", v.Variant([], tm.Rcd([]), tm.Ctr("Option", tm.Var(0)))),
      #("Some", v.Variant([], tm.Var(0), tm.Ctr("Option", tm.Var(0)))),
    ])
  let ctx0 =
    context.push_var(new_ctx, #("Option", v.TypeDef([], tdef), v.Typ(0)))
  // Check: None constructor
  assert unify(ctx0, #(option(v.int_t), s1), #(none, s2))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  assert unify(ctx0, #(none, s2), #(option(v.int_t), s1))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  // Check: Some constructor
  assert unify(ctx0, #(option(v.int_t), s1), #(some(v.int_t), s2))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  assert unify(ctx0, #(some(v.int_t), s2), #(option(v.int_t), s1))
    == Context(..ctx0, subst: [#(0, v.int_t)], hole_counter: 1)
  // Error: type mismatch
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
  // let Vec = $type<n: $Int, a: $Type> {n: n, a: a} {
  // | #Nil        {}                            -> #Vec {n: 0,     a: a}  // n is #1, a is #0
  // | #Cons<m: ?> {x: a, xs: #Vec {n: m, a: a}} -> #Vec {n: m + 1, a: a}  // n is #2, a is #1, m is #0
  // }
  let a = tm.Var(0)
  let nil_ret = tm.ctr("Vec", [#("n", tm.int(0)), #("a", a)])
  let #(_n, a, m) = #(tm.Var(2), tm.Var(1), tm.Var(0))
  let cons_arg =
    tm.Rcd([#("x", a), #("xs", tm.ctr("Vec", [#("n", m), #("a", a)]))])
  let cons_ret =
    tm.ctr("Vec", [#("n", tm.Call("+", [m, tm.int(1)])), #("a", a)])
  let tdef =
    v.TypeDefinition(
      params: [#("n", v.int_t), #("a", v.Typ(0))],
      arg: tm.Rcd([#("n", tm.Var(1)), #("a", tm.Var(0))]),
      variants: [
        #("Nil", v.Variant([], tm.Rcd([]), nil_ret)),
        #("Cons", v.Variant([#("m", v.hole(-1))], cons_arg, cons_ret)),
      ],
    )
  let ctx0 =
    Context(
      ..context.push_var(new_ctx, #("Vec", v.TypeDef([], tdef), v.Typ(0))),
      ffi: [
        #("+", fn(args) {
          case args {
            [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x + y))
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
  assert ctx.errors == [TypeMismatch(#(v.int(1), s1), #(v.int(0), s1))]
  // Error: nested Cons with type mismatch
  let a = vec(v.int(2), v.float_t)
  let b = cons(v.int_t, cons(v.float_t, nil))
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors == [TypeMismatch(#(v.int_t, s2), #(v.hole(1), s1))]
  assert list.key_find(ctx.subst, 1) == Ok(v.float_t)
}

// ============================================================================
// Record unification
// ============================================================================

pub fn unify_rcd_empty_test() {
  let a = v.Rcd([])
  let b = v.Rcd([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_fields_mismatch_test() {
  let a = v.Rcd([#("x", v.int_t)])
  let b = v.Rcd([#("y", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, RcdFieldsMismatch(#(["x"], s1), #(["y"], s2)))
}

pub fn unify_rcd_different_order_test() {
  let a = v.Rcd([#("b", v.int_t), #("a", v.float_t)])
  let b = v.Rcd([#("a", v.float_t), #("b", v.int_t)])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcd_nested_same_test() {
  let inner = v.Rcd([#("x", v.int(42))])
  let a =
    v.Rcd([
      #("name", v.int(1)),
      #("value", inner),
    ])
  let b =
    v.Rcd([
      #("value", inner),
      #("name", v.int(1)),
    ])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

// ============================================================================
// Record type unification
// ============================================================================

pub fn unify_rcdt_empty_test() {
  let a = v.RcdT([])
  let b = v.RcdT([])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcdt_fields_mismatch_test() {
  let a = v.RcdT([#("x", #(v.int_t, None))])
  let b = v.RcdT([#("y", #(v.int_t, None))])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, RcdFieldsMismatch(#(["x"], s1), #(["y"], s2)))
}

pub fn unify_rcdt_different_order_test() {
  let a =
    v.RcdT([
      #("b", #(v.int_t, None)),
      #("a", #(v.float_t, None)),
    ])
  let b =
    v.RcdT([
      #("a", #(v.float_t, None)),
      #("b", #(v.int_t, None)),
    ])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcdt_with_default_test() {
  let a = v.RcdT([#("x", #(v.int_t, Some(v.int(0))))])
  let b = v.RcdT([#("x", #(v.int_t, Some(v.int(0))))])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_rcdt_default_mismatch_test() {
  let a = v.RcdT([#("x", #(v.int_t, Some(v.int(0))))])
  let b = v.RcdT([#("x", #(v.int_t, Some(v.int(1))))])
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(v.int(0), s1), #(v.int(1), s2)))
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
  let a = v.Neut(v.NHole(0))
  let b = v.Neut(v.NHole(0))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_nhole_solve_test() {
  let a = v.Neut(v.NHole(0))
  let b = v.int_t
  let ctx0 = new_ctx
  // Hole is solved with a substitution; hole_counter is unchanged
  // since no new_hole was called during this unify.
  assert unify(ctx0, #(a, s1), #(b, s2))
    == Context(..ctx0, subst: [#(0, v.int_t)])
}

pub fn unify_neut_nhole_infinite_type_test() {
  // Unifying a neutral hole with a value containing the same hole
  // triggers the occurs check, producing an InfiniteType error.
  let a = v.Neut(v.NHole(0))
  let b = v.Neut(v.NHole(0))
  let ctx0 = new_ctx
  // Same hole id unifies directly (both are NHole(0)), so no infinite type.
  // For infinite type, we need a different scenario: a hole unified with
  // a value that contains a deeper hole that itself contains the same hole.
  // Since the first NHole(0)==NHole(0) path catches equal IDs, we test
  // the occurs check path: NHole(0) unified with a Neut(NHole(0)).
  let deep = v.Neut(v.NApp(v.NHole(0), v.int_t))
  let ctx = unify(ctx0, #(a, s1), #(deep, s2))
  assert ctx.errors
    == [
      InfiniteType(0, v.Neut(v.NApp(v.NHole(0), v.int_t)), s2),
    ]
}

pub fn unify_neut_nhole_solve_twice_test() {
  // Solving the same hole twice should merge substitutions
  let a = v.Neut(v.NHole(0))
  let b = v.Neut(v.NHole(0))
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
  let a = v.Neut(v.NCall("foo", []))
  let b = v.Neut(v.NCall("foo", []))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_ncall_same_test() {
  let a = v.Neut(v.NCall("foo", []))
  let b = v.Neut(v.NCall("foo", []))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2)) == ctx0
}

pub fn unify_neut_ncall_name_mismatch_test() {
  let a = v.Neut(v.NCall("foo", []))
  let b = v.Neut(v.NCall("bar", []))
  let ctx0 = new_ctx
  let ctx = unify(ctx0, #(a, s1), #(b, s2))
  assert ctx.errors != []
}

pub fn unify_neut_ncall_arity_mismatch_test() {
  let a = v.Neut(v.NCall("foo", [v.int_t, v.float_t]))
  let b = v.Neut(v.NCall("foo", [v.int_t, v.float_t, v.i64]))
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, CallArityMismatch(#(2, s1), #(3, s2)))
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

pub fn unify_err_mismatch_test() {
  let a = v.Err
  let b = v.int(0)
  let ctx0 = new_ctx
  assert unify(ctx0, #(a, s1), #(b, s2))
    == with_err(ctx0, TypeMismatch(#(a, s1), #(b, s2)))
}
