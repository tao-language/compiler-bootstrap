// ============================================================================
// TAO LANGUAGE CONFIG TESTS
// ============================================================================
/// Tests for the LanguageConfig module.
///
/// Verifies that the LanguageConfig module correctly provides default
/// configurations and helper functions for operator mapping, primitive types,
/// and FFI operator lookup.

import gleeunit
import gleeunit/should
import gleam/list
import gleam/option.{type Option, None, Some}
import tao/language_config.{
  type LanguageConfig,
  type PrimitiveTypes,
  default_config,
  default_primitive_types,
  binary_op_name,
  unary_op_name,
  is_ffi_binary_op,
  is_ffi_unary_op,
  lookup_primitive_type,
  primitive_type_names,
  is_primitive_type,
}
import core/ast as core_ast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// DEFAULT CONFIGURATION TESTS
// ============================================================================

/// Verify that the default config produces the expected truth constructor name.
pub fn default_config_truth_constructor_test() {
  let config = default_config()
  config.truth_constructor |> should.equal("True")
}

/// Verify that the default config produces the expected false constructor name.
pub fn default_config_false_constructor_test() {
  let config = default_config()
  config.false_constructor |> should.equal("False")
}

/// Verify that the default config produces the expected bool type name.
pub fn default_config_bool_type_test() {
  let config = default_config()
  config.bool_type |> should.equal("Bool")
}

/// Verify that the default config produces the expected list constructors.
pub fn default_config_list_constructors_test() {
  let config = default_config()
  config.list_cons |> should.equal("Cons")
  config.list_nil |> should.equal("Nil")
}

// ============================================================================
// BINARY OPERATOR MAPPING TESTS
// ============================================================================

/// Verify that binary operator mapping works for arithmetic operators.
pub fn binary_op_name_add_test() {
  let config = default_config()
  binary_op_name(config, "+") |> should.equal(Some("add"))
}

/// Verify that binary operator mapping works for comparison operators.
pub fn binary_op_name_comparison_test() {
  let config = default_config()
  binary_op_name(config, "==") |> should.equal(Some("eq"))
  binary_op_name(config, "/=") |> should.equal(Some("neq"))
  binary_op_name(config, "<") |> should.equal(Some("lt"))
  binary_op_name(config, ">") |> should.equal(Some("gt"))
  binary_op_name(config, "<=") |> should.equal(Some("lte"))
  binary_op_name(config, ">=") |> should.equal(Some("gte"))
}

/// Verify that binary operator mapping works for logical operators.
pub fn binary_op_name_logical_test() {
  let config = default_config()
  binary_op_name(config, "and") |> should.equal(Some("and"))
  binary_op_name(config, "or") |> should.equal(Some("or"))
}

/// Verify that binary operator mapping works for pipe and concat.
pub fn binary_op_name_special_test() {
  let config = default_config()
  binary_op_name(config, "++") |> should.equal(Some("concat"))
  binary_op_name(config, "|>") |> should.equal(Some("pipe"))
}

/// Verify that unknown operators return None.
pub fn binary_op_name_unknown_test() {
  let config = default_config()
  binary_op_name(config, "unknown") |> should.equal(None)
}

// ============================================================================
// UNARY OPERATOR MAPPING TESTS
// ============================================================================

/// Verify that unary operator mapping works for negate.
pub fn unary_op_name_negate_test() {
  let config = default_config()
  unary_op_name(config, "-") |> should.equal(Some("negate"))
}

/// Verify that unary operator mapping works for not.
pub fn unary_op_name_not_test() {
  let config = default_config()
  unary_op_name(config, "not") |> should.equal(Some("not"))
}

/// Verify that unknown unary operators return None.
pub fn unary_op_name_unknown_test() {
  let config = default_config()
  unary_op_name(config, "unknown") |> should.equal(None)
}

// ============================================================================
// FFI OPERATOR LOOKUP TESTS
// ============================================================================

/// Verify that arithmetic operators are marked as FFI operators.
pub fn is_ffi_binary_op_arithmetic_test() {
  let config = default_config()
  is_ffi_binary_op(config, "add") |> should.be_true()
  is_ffi_binary_op(config, "sub") |> should.be_true()
  is_ffi_binary_op(config, "mul") |> should.be_true()
  is_ffi_binary_op(config, "div") |> should.be_true()
}

/// Verify that comparison operators are marked as FFI operators.
pub fn is_ffi_binary_op_comparison_test() {
  let config = default_config()
  is_ffi_binary_op(config, "eq") |> should.be_true()
  is_ffi_binary_op(config, "neq") |> should.be_true()
  is_ffi_binary_op(config, "lt") |> should.be_true()
  is_ffi_binary_op(config, "gt") |> should.be_true()
  is_ffi_binary_op(config, "lte") |> should.be_true()
  is_ffi_binary_op(config, "gte") |> should.be_true()
}

/// Verify that logical operators are NOT marked as FFI operators.
pub fn is_ffi_binary_op_non_ffi_test() {
  let config = default_config()
  is_ffi_binary_op(config, "and") |> should.be_false()
  is_ffi_binary_op(config, "or") |> should.be_false()
  is_ffi_binary_op(config, "concat") |> should.be_false()
  is_ffi_binary_op(config, "pipe") |> should.be_false()
  is_ffi_binary_op(config, "unknown") |> should.be_false()
}

/// Verify that negate is marked as an FFI unary operator.
pub fn is_ffi_unary_op_negate_test() {
  let config = default_config()
  is_ffi_unary_op(config, "negate") |> should.be_true()
}

/// Verify that not is NOT marked as an FFI unary operator.
pub fn is_ffi_unary_op_not_test() {
  let config = default_config()
  is_ffi_unary_op(config, "not") |> should.be_false()
}

// ============================================================================
// PRIMITIVE TYPES TESTS
// ============================================================================

/// Verify that default primitive types registry contains the expected types.
pub fn default_primitive_types_test() {
  let ptypes = default_primitive_types()
  let names = primitive_type_names(ptypes)
  
  let name_count = list.length(names)
  name_count |> should.equal(6)
}

/// Verify that primitive type lookup works for all types.
pub fn lookup_primitive_type_all_test() {
  let ptypes = default_primitive_types()
  lookup_primitive_type(ptypes, "I32") |> should.equal(Some(core_ast.I32T))
  lookup_primitive_type(ptypes, "I64") |> should.equal(Some(core_ast.I64T))
  lookup_primitive_type(ptypes, "U32") |> should.equal(Some(core_ast.U32T))
  lookup_primitive_type(ptypes, "U64") |> should.equal(Some(core_ast.U64T))
  lookup_primitive_type(ptypes, "F32") |> should.equal(Some(core_ast.F32T))
  lookup_primitive_type(ptypes, "F64") |> should.equal(Some(core_ast.F64T))
}

/// Verify that unknown type names return None.
pub fn lookup_primitive_type_unknown_test() {
  let ptypes = default_primitive_types()
  lookup_primitive_type(ptypes, "String") |> should.equal(None)
  lookup_primitive_type(ptypes, "Bool") |> should.equal(None)
  lookup_primitive_type(ptypes, "unknown") |> should.equal(None)
}

/// Verify that is_primitive_type works correctly.
pub fn is_primitive_type_test() {
  let ptypes = default_primitive_types()
  is_primitive_type(ptypes, "I32") |> should.be_true()
  is_primitive_type(ptypes, "F64") |> should.be_true()
  is_primitive_type(ptypes, "String") |> should.be_false()
  is_primitive_type(ptypes, "Bool") |> should.be_false()
}

/// Verify that primitive type names include all expected types.
pub fn primitive_type_names_test() {
  let ptypes = default_primitive_types()
  let names = primitive_type_names(ptypes)
  
  list.all(names, fn(name) {
    case name {
      "I32" -> True
      "I64" -> True
      "U32" -> True
      "U64" -> True
      "F32" -> True
      "F64" -> True
      _ -> False
    }
  }) |> should.be_true()
}
