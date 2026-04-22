// ============================================================================
// INFER UTILITIES TESTS
// ============================================================================
/// Tests for the infer utilities module.
///
/// These helper functions are used by the type checker during inference.

import core/ast as ast
import core/infer_utils as infer_utils
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

const span = Span("infer_utils_test", 1, 1, 1, 1)

fn vhole(id) { ast.VNeut(ast.HHole(id), []) }
fn hvar(lvl) { ast.VNeut(ast.HVar(lvl), []) }
fn vlitt(t) { ast.VLitT(t) }

// ============================================================================
// COERCE TO TYPE
// ============================================================================

pub fn coerce_to_type_accepts_hole_test() {
  // When target is a hole, any term is accepted
  let term = ast.Typ(0, span)
  let target = vhole(0)
  let result = infer_utils.coerce_to_type(term, target)
  result |> should.equal(term)
}

pub fn coerce_to_type_accepts_known_type_test() {
  // When target is a known type, term is accepted as-is
  let term = ast.Typ(0, span)
  let target = vlitt(ast.I32T)
  let result = infer_utils.coerce_to_type(term, target)
  result |> should.equal(term)
}

// ============================================================================
// IS TRUTH VALUE
// ============================================================================

pub fn is_truth_value_true_test() {
  // VNeut(HHole(_), [VNeut(HHole(1), [])]) should be treated as truth
  let truth_val = ast.VCtrValue(ast.VCtr("True", ast.VLitT(ast.I32T)))
  infer_utils.is_truth_value(truth_val, "True") |> should.be_true
}

pub fn is_truth_value_false_test() {
  let val = ast.VLitT(ast.I32T)
  infer_utils.is_truth_value(val, "True") |> should.be_false
}

// ============================================================================
// TYPES EQUAL
// ============================================================================

pub fn types_equal_same_test() {
  let t1 = vlitt(ast.I32T)
  let t2 = vlitt(ast.I32T)
  infer_utils.types_equal(t1, t2) |> should.be_true
}

pub fn types_equal_different_test() {
  let t1 = vlitt(ast.I32T)
  let t2 = vlitt(ast.I64T)
  infer_utils.types_equal(t1, t2) |> should.be_false
}

// ============================================================================
// IS HOLE VALUE
// ============================================================================

pub fn is_hole_value_true_test() {
  infer_utils.is_hole_value(vhole(42)) |> should.be_true
}

pub fn is_hole_value_false_test() {
  infer_utils.is_hole_value(ast.VLitT(ast.I32T)) |> should.be_false
  infer_utils.is_hole_value(hvar(0)) |> should.be_false
}

// ============================================================================
// IS VAR VALUE
// ============================================================================

pub fn is_var_value_true_test() {
  infer_utils.is_var_value(hvar(5)) |> should.be_true
}

pub fn is_var_value_false_test() {
  infer_utils.is_var_value(vhole(0)) |> should.be_false
  infer_utils.is_var_value(ast.VLitT(ast.I32T)) |> should.be_false
}

// ============================================================================
// IS UNRESOLVED
// ============================================================================

pub fn is_unresolved_hole_test() {
  infer_utils.is_unresolved(vhole(1)) |> should.be_true
}

pub fn is_unresolved_var_test() {
  infer_utils.is_unresolved(hvar(2)) |> should.be_true
}

pub fn is_unresolved_literl_test() {
  infer_utils.is_unresolved(ast.VLitT(ast.I32T)) |> should.be_false
}

// ============================================================================
// GET VAR LEVEL
// ============================================================================

pub fn get_var_level_ok_test() {
  infer_utils.get_var_level(hvar(42)) |> should.equal(Ok(42))
}

pub fn get_var_level_error_test() {
  infer_utils.get_var_level(ast.VLitT(ast.I32T)) |> should.equal(Error(Nil))
  infer_utils.get_var_level(vhole(0)) |> should.equal(Error(Nil))
}

// ============================================================================
// IS LIT T
// ============================================================================

pub fn is_lit_t_true_test() {
  infer_utils.is_lit_t(vlitt(ast.I32T)) |> should.be_true
  infer_utils.is_lit_t(vlitt(ast.I64T)) |> should.be_true
  infer_utils.is_lit_t(vlitt(ast.F64T)) |> should.be_true
}

pub fn is_lit_t_false_test() {
  infer_utils.is_lit_t(vhole(0)) |> should.be_false
  infer_utils.is_lit_t(hvar(0)) |> should.be_false
}
