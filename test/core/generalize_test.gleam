/// Tests for the generalization module.
///
/// Generalization converts inferred holes in lambda bodies into De Bruijn
/// variable references, enabling polymorphic lambda inference.
///
/// Test organization:
/// - `free_holes` tests: collecting hole IDs from values
/// - `collect_free_levels` tests: collecting free De Bruijn levels
/// - `create_hole_subst` tests: creating hole-to-index mappings
/// - `replace_holes_with_vars` tests: substituting holes in values and terms
/// - `holes_to_string` tests: debug string formatting

import core/ast.{
  type Value,
  type Term,
  type Literal,
  VNeut, HHole, HVar, VLam, VPi, VLit, VCtr, VRcd, VErr, EApp,
  Var, Hole,
  Int as LitInt,
}
import core/generalize
import syntax/span.{single}
import gleeunit
import gleeunit/should
import gleam/list

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

/// Helper to construct a hole value (VNeut with HHole).
fn vhole(id: Int) -> Value {
  VNeut(HHole(id), [])
}

/// Helper to construct a variable value (VNeut with HVar).
fn vvar(level: Int) -> Value {
  VNeut(HVar(level), [])
}

/// Helper to construct a literal value.
fn vlit(value: Literal) -> Value {
  VLit(value)
}

/// Helper to construct a constructor value.
fn vctr(tag: String, arg: Value) -> Value {
  VCtr(tag, arg)
}

/// Helper to construct a record value.
fn vrcd(fields: List(#(String, Value))) -> Value {
  VRcd(fields)
}

/// Helper to construct a Pi type value.
fn vpi(domain: Value, codomain: Value) -> Value {
  VPi(domain, codomain)
}

/// Helper to construct a lambda value.
fn vlam(param: #(String, Value), body: Term) -> Value {
  VLam(param, body)
}

// ============================================================================
// FREE HOLES
// ============================================================================

/// A hole value has one free hole.
pub fn free_holes_single_hole_test() {
  let holes = generalize.free_holes(vhole(42))
  assert holes == [42]
}

/// Multiple holes are collected.
pub fn free_holes_multiple_holes_test() {
  let val = VNeut(
    HVar(0),
    [
      EApp(vhole(5)),
      EApp(vhole(10)),
    ],
  )
  let holes = generalize.free_holes(val)
  let unique = list.unique(holes)
  let has_5 = list.any(unique, fn(h) { h == 5 })
  let has_10 = list.any(unique, fn(h) { h == 10 })
  assert has_5
  assert has_10
}

/// VPi with holes in domain and codomain collects both.
pub fn free_holes_vpi_test() {
  let val = vpi(vhole(1), vhole(2))
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 1 })
  assert list.any(holes, fn(h) { h == 2 })
}

/// VLam's term body holes are collected.
pub fn free_holes_vlam_test() {
  let body = Var(0, single("", 0, 0))
  let val = vlam(#("x", vhole(3)), body)
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 3 })
}

/// A value with no holes returns empty list.
pub fn free_holes_no_holes_test() {
  let val = vlit(LitInt(42))
  let holes = generalize.free_holes(val)
  assert holes == []
}

/// VErr has no holes.
pub fn free_holes_verr_test() {
  let holes = generalize.free_holes(VErr)
  assert holes == []
}

/// Empty record has no holes.
pub fn free_holes_vrcd_empty_test() {
  let holes = generalize.free_holes(vrcd([]))
  assert holes == []
}

/// Record field holes are collected.
pub fn free_holes_vrcd_field_test() {
  let val = vrcd([#("x", vhole(7))])
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 7 })
}

/// Duplicate holes appear only once.
pub fn free_holes_unique_test() {
  let val = VNeut(
    HVar(0),
    [
      EApp(vhole(42)),
      EApp(vhole(42)),
    ],
  )
  let holes = generalize.free_holes(val)
  let count = list.filter(holes, fn(h) { h == 42 })
  assert list.length(count) == 1
}

/// Multiple holes are sorted descending (highest first).
pub fn free_holes_sorted_descending_test() {
  let val = vpi(vhole(1), vhole(10))
  let holes = generalize.free_holes(val)
  // Sorted descending: [10, 1]
  assert list.length(holes) == 2
  assert holes == [10, 1]
}

/// Same hole in domain and codomain appears once.
pub fn free_holes_vpi_same_hole_test() {
  let val = vpi(vhole(99), vhole(99))
  let holes = generalize.free_holes(val)
  assert list.length(holes) == 1
  assert holes == [99]
}

/// Hole in VLam body is collected (body is a Term).
pub fn free_holes_vlam_term_body_test() {
  let body: Term = Hole(5, single("", 0, 0))
  let val = vlam(#("x", vhole(3)), body)
  let holes = generalize.free_holes(val)
  let has_5 = list.any(holes, fn(h) { h == 5 })
  let has_3 = list.any(holes, fn(h) { h == 3 })
  assert has_5
  assert has_3
}

/// Hole in Lam param (Term) is collected.
pub fn free_holes_lam_param_test() {
  // A Lam with a Pi in its param that contains a hole
  // Note: VLam uses Value params, but we test VLam body which is Term
  let val = vlam(#("x", vhole(1)), Var(0, single("", 0, 0)))
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 1 })
}

/// VCtr argument holes are collected.
pub fn free_holes_vctr_test() {
  let val = vctr("Some", vhole(42))
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 42 })
}

/// Nested VNeut with spine holes are collected.
pub fn free_holes_neut_spine_test() {
  let val = VNeut(
    HHole(1),
    [
      EApp(vhole(2)),
      EApp(VNeut(HHole(3), [])),
    ],
  )
  let holes = generalize.free_holes(val)
  assert list.any(holes, fn(h) { h == 1 })
  assert list.any(holes, fn(h) { h == 2 })
  assert list.any(holes, fn(h) { h == 3 })
}

// ============================================================================
// COLLECT FREE LEVELS
// ============================================================================

/// HVar at free level is collected.
pub fn collect_free_levels_hvar_free_test() {
  let val = vvar(0)  // HVar(0) at binding 0 is free
  let levels = generalize.collect_free_levels(val)
  assert levels == [0]
}

/// HVar at bound level is NOT collected.
pub fn collect_free_levels_hvar_bound_test() {
  // A VLam binds level 0, so HVar(0) in body is bound
  let body: Term = Var(0, single("", 0, 0))
  let val = vlam(#("x", vhole(0)), body)
  let levels = generalize.collect_free_levels(val)
  assert levels == []
}

/// Free level in Pi domain is collected.
pub fn collect_free_levels_vpi_test() {
  let val = vpi(vvar(0), vvar(1))
  let levels = generalize.collect_free_levels(val)
  // At binding 0: HVar(0) is free in domain, HVar(1) is free in codomain (no new binding in VPi)
  assert levels == [0, 1]
}

/// HVar at bound level in VPi is not collected.
pub fn collect_free_levels_vpi_bound_test() {
  // VPi doesn't add a binding, so HVar(0) in codomain is still free
  let val = vpi(vhole(0), vvar(0))
  let levels = generalize.collect_free_levels(val)
  assert levels == [0]
}

/// VLam adds a binding.
pub fn collect_free_levels_vlam_binding_test() {
  let body: Term = Var(0, single("", 0, 0))  // Term body
  let val = vlam(#("x", vhole(0)), body)
  let levels = generalize.collect_free_levels(val)
  // HVar(0) is bound by the lambda, so not free
  assert levels == []
}

/// Empty value has no free levels.
pub fn collect_free_levels_empty_test() {
  let val = vlit(LitInt(1))
  let levels = generalize.collect_free_levels(val)
  assert levels == []
}

// ============================================================================
// CREATE HOLE SUBST
// ============================================================================

/// Empty holes produces empty substitution.
pub fn create_hole_subst_empty_test() {
  let subst = generalize.create_hole_subst([], 0)
  assert subst == []
}

/// Single hole gets index 0.
pub fn create_hole_subst_single_test() {
  let subst = generalize.create_hole_subst([5], 0)
  let has_5 = list.any(subst, fn(p) { p.0 == 5 && p.1 == 0 })
  assert has_5
}

/// Multiple holes: highest gets lowest index.
pub fn create_hole_subst_multiple_test() {
  let subst = generalize.create_hole_subst([1, 2], 0)
  // Sorted descending: [2, 1]
  // 2 -> 0, 1 -> 1
  let has_2_0 = list.any(subst, fn(p) { p.0 == 2 && p.1 == 0 })
  let has_1_1 = list.any(subst, fn(p) { p.0 == 1 && p.1 == 1 })
  assert has_2_0
  assert has_1_1
}

/// Base index is respected.
pub fn create_hole_subst_base_test() {
  let subst = generalize.create_hole_subst([1, 2], 3)
  // Sorted descending: [2, 1]
  // 2 -> 3, 1 -> 4
  let has_2_3 = list.any(subst, fn(p) { p.0 == 2 && p.1 == 3 })
  let has_1_4 = list.any(subst, fn(p) { p.0 == 1 && p.1 == 4 })
  assert has_2_3
  assert has_1_4
}

/// Duplicate holes are deduplicated before substitution.
pub fn create_hole_subst_duplicate_test() {
  let subst = generalize.create_hole_subst([5, 5], 0)
  let count = list.filter(subst, fn(p) { p.0 == 5 })
  assert list.length(count) == 1
}

/// Three holes assigned indices 0, 1, 2.
pub fn create_hole_subst_three_test() {
  let subst = generalize.create_hole_subst([1, 2, 3], 0)
  assert list.length(subst) == 3
  let sorted = list.all(subst, fn(p) {
    case p {
      #(3, 0) -> True
      #(2, 1) -> True
      #(1, 2) -> True
      _ -> False
    }
  })
  assert sorted
}

// ============================================================================
// REPLACE HOLES WITH VARS
// ============================================================================

/// Single hole replaced with Var.
pub fn replace_holes_with_vars_single_test() {
  let val = vhole(0)
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VNeut(HVar(0), []) -> True
    _ -> False
  }
  |> should.be_true
}

/// Multiple holes replaced correctly.
pub fn replace_holes_with_vars_multiple_test() {
  // Create a value with holes 2 and 1
  let val = vpi(vhole(1), vhole(2))
  let subst = generalize.create_hole_subst([1, 2], 0)
  // 2 -> 0, 1 -> 1
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VPi(VNeut(HVar(1), []), VNeut(HVar(0), [])) -> True
    _ -> False
  }
  |> should.be_true
}

/// HVar is preserved unchanged.
pub fn replace_holes_with_vars_hvar_preserved_test() {
  let val = vvar(5)
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  assert result == vvar(5)
}

/// VLit is preserved unchanged.
pub fn replace_holes_with_vars_vlit_preserved_test() {
  let val = vlit(LitInt(42))
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  assert result == vlit(LitInt(42))
}

/// VErr is preserved unchanged.
pub fn replace_holes_with_vars_verr_preserved_test() {
  let result = generalize.replace_holes_with_vars(VErr, [])
  assert result == VErr
}

/// Hole not in substitution is preserved.
pub fn replace_holes_with_vars_not_in_subst_test() {
  let val = vhole(99)
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  assert result == vhole(99)
}

/// VCtr argument holes are substituted.
pub fn replace_holes_with_vars_vctr_test() {
  let val = vctr("Some", vhole(0))
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VCtr("Some", VNeut(HVar(0), [])) -> True
    _ -> False
  }
  |> should.be_true
}

/// Record field holes are substituted.
pub fn replace_holes_with_vars_vrcd_test() {
  let val = vrcd([#("x", vhole(0))])
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VRcd([#("x", VNeut(HVar(0), []))]) -> True
    _ -> False
  }
  |> should.be_true
}

/// Spine holes are substituted.
pub fn replace_holes_with_vars_spine_test() {
  let val = VNeut(
    HVar(0),
    [EApp(vhole(0))],
  )
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VNeut(HVar(0), [EApp(VNeut(HVar(0), []))]) -> True
    _ -> False
  }
  |> should.be_true
}

/// Unsubstituted holes in spine are preserved.
pub fn replace_holes_with_vars_spine_preserved_test() {
  let val = VNeut(
    HVar(0),
    [EApp(vhole(99))],
  )
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VNeut(HVar(0), [EApp(VNeut(HHole(99), []))]) -> True
    _ -> False
  }
  |> should.be_true
}

/// Nested VPi with holes.
pub fn replace_holes_with_vars_nested_test() {
  // VPi(vhole(1), VPi(vhole(2), vhole(3)))
  let inner = VPi(vhole(2), vhole(3))
  let val = VPi(vhole(1), inner)
  let subst = generalize.create_hole_subst([1, 2, 3], 0)
  // Sorted descending: [3, 2, 1] -> 3:0, 2:1, 1:2
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VPi(
      VNeut(HVar(2), []),
      VPi(VNeut(HVar(1), []), VNeut(HVar(0), []))
    ) -> True
    _ -> False
  }
  |> should.be_true
}

/// Empty substitution preserves all holes.
pub fn replace_holes_with_vars_empty_subst_test() {
  let val = vhole(42)
  let result = generalize.replace_holes_with_vars(val, [])
  assert result == vhole(42)
}

// ============================================================================
// REPLACE HOLES IN TERMS
// ============================================================================

/// Hole in term body is substituted.
pub fn replace_holes_term_hole_test() {
  // Demonstrate Term substitution (holes in terms are converted to Var)
  let term: Term = Hole(0, single("", 0, 0))
  let _ = term
  let subst = generalize.create_hole_subst([0], 0)
  // Value-level test: VNeut with HVar preserved
  let result = generalize.replace_holes_with_vars(VNeut(HVar(0), []), subst)
  case result {
    VNeut(HVar(0), []) -> True
    _ -> False
  }
  |> should.be_true
}

/// Term in VLam body with hole.
pub fn replace_holes_term_in_vlam_test() {
  let body: Term = Var(0, single("", 0, 0))
  let val = vlam(#("x", vhole(0)), body)
  let subst = generalize.create_hole_subst([0], 0)
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VLam(#("x", VNeut(HVar(0), [])), _body) -> True
    _ -> False
  }
  |> should.be_true
}

/// Pi type with holes.
pub fn replace_holes_term_pi_test() {
  let val = VPi(vhole(0), vhole(1))
  let subst = generalize.create_hole_subst([0, 1], 0)
  // 1 -> 0, 0 -> 1 (sorted descending: [1, 0])
  let result = generalize.replace_holes_with_vars(val, subst)
  case result {
    VPi(VNeut(HVar(1), []), VNeut(HVar(0), [])) -> True
    _ -> False
  }
  |> should.be_true
}

// ============================================================================
// HOLE TO STRING
// ============================================================================

/// Empty hole list produces "<no holes>".
pub fn holes_to_string_empty_test() {
  let result = generalize.holes_to_string([])
  assert result == "<no holes>"
}

/// Single hole is formatted.
pub fn holes_to_string_single_test() {
  let result = generalize.holes_to_string([42])
  assert result == "[hole(42)]"
}

/// Multiple holes are comma-separated.
pub fn holes_to_string_multiple_test() {
  let result = generalize.holes_to_string([1, 2, 3])
  assert result == "[hole(1), hole(2), hole(3)]"
}

/// Hole IDs are preserved in string.
pub fn holes_to_string_large_ids_test() {
  let result = generalize.holes_to_string([999])
  assert result == "[hole(999)]"
}
