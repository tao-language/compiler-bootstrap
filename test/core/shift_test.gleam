/// Unit tests for shift_term_from — De Bruijn index shifting correctness.
///
/// These tests verify that shift_term_from correctly shifts indices >= `from`
/// while preserving indices < `from`. This is critical for GADT inference
/// where constructor-bound variables (indices 0..n-1) must NOT be shifted
/// when type parameters (indices n..) are removed from the environment.
///
/// Tests are written inductively: 0 bindings, 1 binding, 2 bindings.
/// If 0, 1, and 2 all pass, the function works for any number of bindings.

import core/ast.{
  type Term,
  Ann, App, Call, Ctr, EApp, Err, Float as LitFloat, HHole, HVar, Hole,
  Int as LitInt, Lam, Lit, Match, PAny, PCtr, PLit, PUnit, PVar, Pi,
  Rcd, RcdT, Typ, VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, VRcdT, Var,
  shift_term_from, term_to_string,
}
import gleam/option.{Some, None}
import gleam/list
import gleeunit
import syntax/span.{type Span, single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// ZERO BINDINGS / PARAMETERS (from = 0, shift = 0)
// No indices should be shifted when from = 0 and shift = 0.
// ============================================================================

pub fn shift_zero_bindings_no_op_test() {
  // With 0 type params, from=0 and shift=0 means no indices shift.
  // This is the base case: an empty environment, nothing to adjust.
  let t = Var(0, single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, 0, 0)
  assert shifted == Var(0, single("file.gleam", 1, 1))
}

pub fn shift_zero_bindings_multiple_vars_test() {
  // Multiple variables at different indices, all >= 0, all shifted by 0.
  let t = App(
    Var(0, single("file.gleam", 1, 1)),
    Var(2, single("file.gleam", 1, 2)),
    single("file.gleam", 1, 3),
  )
  let shifted = shift_term_from(t, 0, 0)
  assert shifted == App(
    Var(0, single("file.gleam", 1, 1)),
    Var(2, single("file.gleam", 1, 2)),
    single("file.gleam", 1, 3),
  )
}

// ============================================================================
// ONE BINDING (from = 1, shift = -1)
// Indices >= 1 shift by -1; index 0 is preserved.
// Models: 1 constructor-bound variable (@m), 1 type param (a).
// Environment: [m, a]. Result: Var(0)=m (preserved), Var(1)=a -> Var(0)=a.
// ============================================================================

pub fn shift_one_binding_preserves_index_zero_test() {
  // Index 0 (constructor-bound var @m) is preserved.
  let t = Var(0, single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, -1, 1)
  assert shifted == Var(0, single("file.gleam", 1, 1))
}

pub fn shift_one_binding_shifts_type_param_test() {
  // Index 1 (type param a) shifts to index 0 after removing the type param.
  let t = Var(1, single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, -1, 1)
  assert shifted == Var(0, single("file.gleam", 1, 1))
}

pub fn shift_one_binding_nested_in_app_test() {
  // App with one bound var (index 0) and one type param (index 1).
  let span1 = single("file.gleam", 1, 1)
  let span2 = single("file.gleam", 1, 2)
  let span3 = single("file.gleam", 1, 3)
  let t = App(
    Var(0, span1), // @m preserved
    Var(1, span2), // a shifts to 0
    span3,
  )
  let shifted = shift_term_from(t, -1, 1)
  let span0 = single("file.gleam", 1, 1)
  let span2s = single("file.gleam", 1, 2)
  assert shifted == App(
    Var(0, span0), // still @m
    Var(0, span2s), // now refers to a (was index 1)
    span3,
  )
}

pub fn shift_one_binding_lambda_test() {
  // Lambda body: Var(0) is bound by the lambda itself, Var(1) is @m (preserved).
  // When shifting the lambda by -1, from for the body becomes 1 + 0 + 1 = 2.
  // Var(1) < 2, so it stays Var(1) (it refers to @m, not the lambda's binder).
  let body = Var(1, single("file.gleam", 1, 1)) // @m in body
  let lam = Lam([], #("a", Hole(-1, single("file.gleam", 1, 1))), body, single("file.gleam", 1, 2))
  let shifted = shift_term_from(lam, -1, 1)
  // Var(1) < 2 (body's from), so it stays Var(1) (preserved, refers to @m)
  assert shifted
    == Lam([], #("a", Hole(-1, single("file.gleam", 1, 1))), Var(1, single("file.gleam", 1, 1)), single("file.gleam", 1, 2))
}

// ============================================================================
// TWO BINDINGS (from = 2, shift = -2)
// Indices >= 2 shift by -2; indices 0, 1 are preserved.
// Models: 2 constructor-bound variables (@m, @n), 1 type param (a).
// Environment: [m, n, a]. Result: Var(0)=m, Var(1)=n (preserved), Var(2)=a -> Var(0)=a.
// ============================================================================

pub fn shift_two_bindings_preserves_indices_zero_and_one_test() {
  // Both constructor-bound vars (indices 0 and 1) are preserved.
  let t0 = Var(0, single("file.gleam", 1, 1))
  let t1 = Var(1, single("file.gleam", 1, 1))
  let shifted0 = shift_term_from(t0, -2, 2)
  let shifted1 = shift_term_from(t1, -2, 2)
  assert shifted0 == Var(0, single("file.gleam", 1, 1))
  assert shifted1 == Var(1, single("file.gleam", 1, 1))
}

pub fn shift_two_bindings_shifts_type_param_test() {
  // Index 2 (type param a) shifts to index 0 after removing 2 type params.
  let t = Var(2, single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, -2, 2)
  assert shifted == Var(0, single("file.gleam", 1, 1))
}

pub fn shift_two_bindings_three_vars_test() {
  // Three variables: m(0), n(1), a(2).
  // m and n preserved, a shifts from 2 to 0.
  let span1 = single("file.gleam", 1, 1)
  let span2 = single("file.gleam", 1, 2)
  let span3 = single("file.gleam", 1, 3)
  let span4 = single("file.gleam", 1, 4)
  let t = App(
    App(Var(0, span1), Var(1, span2), span2),
    Var(2, span3),
    span4,
  )
  let shifted = shift_term_from(t, -2, 2)
  assert shifted == App(
    App(Var(0, span1), Var(1, span2), span2),
    Var(0, span3),
    span4,
  )
}

pub fn shift_two_bindings_deeply_nested_test() {
  // Deeply nested: Var(0)=m, Var(1)=n, Var(2)=a, Var(3)=b (another param).
  // m(0) and n(1) preserved. a(2)->0, b(3)->1.
  let s1 = single("file.gleam", 1, 1)
  let s2 = single("file.gleam", 1, 2)
  let s3 = single("file.gleam", 1, 3)
  let s4 = single("file.gleam", 1, 4)
  let s5 = single("file.gleam", 1, 5)
  // t = App(b, App(a, n, s3), s5) where b=Var(3), a=Var(2), n=Var(1)
  let inner = App(
    Var(2, s2), // a
    Var(1, s3), // n
    s3,
  )
  let t = App(
    Var(3, s1), // b
    inner,
    s5,
  )
  let shifted = shift_term_from(t, -2, 2)
  let expected_inner = App(
    Var(0, s2), // a -> 0
    Var(1, s3), // n -> 1 (preserved)
    s3,
  )
  let expected = App(
    Var(1, s1), // b -> 1
    expected_inner,
    s5,
  )
  assert shifted == expected
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn shift_hole_unchanged_test() {
  // Holes are never shifted regardless of from/shift.
  let t = Hole(42, single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, -5, 10)
  assert shifted == Hole(42, single("file.gleam", 1, 1))
}

pub fn shift_lit_unchanged_test() {
  // Literals are never shifted.
  let t = Lit(LitInt(42), single("file.gleam", 1, 1))
  let shifted = shift_term_from(t, -100, 0)
  assert shifted == Lit(LitInt(42), single("file.gleam", 1, 1))
}

pub fn shift_nested_lambda_preserves_inner_binder_test() {
  // Nested lambda: inner lambda's binder (Var(0)) should NOT shift
  // because from is adjusted for the inner binder.
  let inner_body = Var(0, single("file.gleam", 1, 1))
  let inner_lam = Lam([], #("x", Hole(-1, single("file.gleam", 1, 1))), inner_body, single("file.gleam", 1, 2))
  let outer_body = inner_lam
  let outer_lam = Lam([], #("y", Hole(-1, single("file.gleam", 1, 3))), outer_body, single("file.gleam", 1, 4))
  // Shift by -1, from=1 (outer lambda's binder).
  // The inner lambda's Var(0) is < 1+1=2, so it stays Var(0).
  let shifted = shift_term_from(outer_lam, -1, 1)
  assert shifted
    == Lam(
      [],
      #("y", Hole(-1, single("file.gleam", 1, 3))),
      Lam(
        [],
        #("x", Hole(-1, single("file.gleam", 1, 1))),
        Var(0, single("file.gleam", 1, 1)),
        single("file.gleam", 1, 2),
      ),
      single("file.gleam", 1, 4),
    )
}

pub fn shift_call_shifts_all_args_test() {
  // Call with multiple typed arguments.
  let s1 = single("file.gleam", 1, 1)
  let s2 = single("file.gleam", 1, 2)
  let s3 = single("file.gleam", 1, 3)
  let s4 = single("file.gleam", 1, 4)
  let s5 = single("file.gleam", 1, 5)
  let s6 = single("file.gleam", 1, 6)
  let t = Call(
    "add",
    [#(Var(0, s1), Var(2, s2)),
     #(Var(1, s3), Var(3, s4))],
    Var(2, s5),
    s6,
  )
  // from=2: Var(0) and Var(1) preserved, Var(2)->0, Var(3)->1
  let shifted = shift_term_from(t, -2, 2)
  assert shifted == Call(
    "add",
    [#(Var(0, s1), Var(0, s2)),
     #(Var(1, s3), Var(1, s4))],
    Var(0, s5),
    s6,
  )
}

// ============================================================================
// INDUCTIVE COROLLARY: 3 bindings (from=3, shift=-3)
// If 0, 1, and 2 work, 3 should work too. This confirms the pattern.
// ============================================================================

pub fn shift_three_bindings_preserves_first_three_test() {
  // Three constructor-bound vars (0,1,2) preserved, type param (3) shifts to 0.
  let s1 = single("file.gleam", 1, 1)
  let s2 = single("file.gleam", 1, 2)
  let s3 = single("file.gleam", 1, 3)
  let s4 = single("file.gleam", 1, 4)
  let s5 = single("file.gleam", 1, 5)
  let t = App(
    App(App(Var(0, s1), Var(1, s2), s2), Var(2, s3), s3),
    Var(3, s4),
    s5,
  )
  let shifted = shift_term_from(t, -3, 3)
  assert shifted == App(
    App(App(Var(0, s1), Var(1, s2), s2), Var(2, s3), s3),
    Var(0, s4),
    s5,
  )
}
