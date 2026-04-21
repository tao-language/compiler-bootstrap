// ============================================================================
// LITERAL HELPER TESTS
// Tests for extracted helper functions: try_coerce_literal, lit_types_unify, is_true
// ============================================================================
import core/ast as ast
import core/eval as eval
import core/unify as unify
import core/infer as infer
import gleam/option.{type Option, Some, None}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TRY_COERCE_LITERAL TESTS
// ============================================================================

pub fn coerce_int_to_i32_test() {
  let result = infer.try_coerce_literal(ast.IntLit(42), ast.VLitT(ast.I32T))
  case result {
    Some(ast.VLit(ast.I32(42))) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn coerce_int_to_f64_test() {
  let result = infer.try_coerce_literal(ast.IntLit(99), ast.VLitT(ast.F64T))
  case result {
    Some(ast.VLit(ast.F64(99.0))) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn coerce_float_to_f32_test() {
  let result = infer.try_coerce_literal(ast.FloatLit(3.14), ast.VLitT(ast.F32T))
  case result {
    Some(ast.VLit(ast.F32(3.14))) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn coerce_intlit_to_ilitt_test() {
  let result = infer.try_coerce_literal(ast.IntLit(1), ast.VLitT(ast.ILitT))
  case result {
    Some(ast.VLit(ast.IntLit(1))) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn coerce_concrete_literal_returns_none_test() {
  // I32 literal to I64T should NOT coerce (concrete literal needs unification)
  let result = infer.try_coerce_literal(ast.I32(42), ast.VLitT(ast.I64T))
  result |> should.equal(None)
}

pub fn coerce_u64t_literal_type_not_literal_test() {
  // U64T is a LiteralType (type), not a Literal (value)
  // We can't pass it to try_coerce_literal which expects ast.Literal
  // This test ensures the function properly rejects non-literal inputs
  // by checking that None is returned for non-matching patterns
  let result = infer.try_coerce_literal(ast.IntLit(0), ast.VTyp(0))
  result |> should.equal(None)
}

// ============================================================================
// LITERAL_TYPES_UNIFY TESTS
// ============================================================================

pub fn ilitt_unifies_with_concrete_int_test() {
  unify.lit_types_unify(ast.VLitT(ast.ILitT), ast.VLitT(ast.I32T))
  |> should.equal(True)
}

pub fn ilitt_unifies_with_float_test() {
  unify.lit_types_unify(ast.VLitT(ast.ILitT), ast.VLitT(ast.F64T))
  |> should.equal(True)
}

pub fn concrete_int_unifies_with_ilitt_test() {
  unify.lit_types_unify(ast.VLitT(ast.I64T), ast.VLitT(ast.ILitT))
  |> should.equal(True)
}

pub fn flitt_unifies_with_float_test() {
  unify.lit_types_unify(ast.VLitT(ast.FLitT), ast.VLitT(ast.F32T))
  |> should.equal(True)
}

pub fn same_concrete_types_unify_test() {
  unify.lit_types_unify(ast.VLitT(ast.I32T), ast.VLitT(ast.I32T))
  |> should.equal(True)
}

pub fn incompatible_types_do_not_unify_test() {
  // I32T and I64T are both concrete - should NOT unify
  unify.lit_types_unify(ast.VLitT(ast.I32T), ast.VLitT(ast.I64T))
  |> should.equal(False)
}

pub fn flitt_does_not_unify_with_int_test() {
  // FLitT only unifies with float types, not integer types
  unify.lit_types_unify(ast.VLitT(ast.FLitT), ast.VLitT(ast.I32T))
  |> should.equal(False)
}

pub fn non_literal_types_return_false_test() {
  unify.lit_types_unify(ast.VTyp(0), ast.VTyp(1))
  |> should.equal(False)
}

// ============================================================================
// IS_TRUE TESTS
// ============================================================================

pub fn is_true_true_constructor_test() {
  let true_val = ast.VCtrValue(ast.VCtr("True", ast.VUnit))
  ast.is_true_value(true_val)
  |> should.equal(True)
}

pub fn is_true_false_constructor_test() {
  let false_val = ast.VCtrValue(ast.VCtr("False", ast.VUnit))
  ast.is_true_value(false_val)
  |> should.equal(False)
}

pub fn is_true_other_constructor_test() {
  let other_val = ast.VCtrValue(ast.VCtr("Some", ast.VLit(ast.I32(42))))
  ast.is_true_value(other_val)
  |> should.equal(False)
}

pub fn is_true_literal_test() {
  let lit_val = ast.VLit(ast.I32(42))
  ast.is_true_value(lit_val)
  |> should.equal(False)
}

pub fn is_true_unit_test() {
  ast.is_true_value(ast.VUnit)
  |> should.equal(False)
}
