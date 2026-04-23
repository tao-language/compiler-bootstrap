// ============================================================================
// TAO LANGUAGE CONFIGURATION
// ============================================================================
/// Configuration for the Tao language layer.
///
/// This module provides a single source of truth for all language-specific
/// names and mappings that the desugarer and FFI need. This makes it possible
/// to swap out or modify language conventions without changing compiler code.
///
/// For detailed documentation see:
/// - [Language Layer Architecture](../../docs/plans/tao/language-layer.md)

import gleam/dict
import gleam/list
import gleam/option.{type Option, Some, None}
import core/ast as core_ast

// ============================================================================
// LANGUAGE CONFIG
// ============================================================================

/// Configuration for a language that compiles to Core.
///
/// This is passed through the DesugarContext and FFI layer to avoid
/// hardcoded assumptions about specific type/constructor/operator names.
pub type LanguageConfig {
  LanguageConfig(
    /// Truth constructor name for control flow (e.g., "True")
    truth_constructor: String,
    /// False constructor name (e.g., "False")
    false_constructor: String,
    /// Boolean type name used for comparison operator results (e.g., "Bool")
    bool_type: String,
    /// Constructor used for list cons cells (e.g., "Cons")
    list_cons: String,
    /// Constructor used for empty lists (e.g., "Nil")
    list_nil: String,
    /// Mapping from binary operator token to function name
    /// e.g., "+" -> "add", "==" -> "eq"
    binary_ops: dict.Dict(String, String),
    /// Mapping from unary operator token to function name
    /// e.g., "-" -> "negate", "not" -> "not"
    unary_ops: dict.Dict(String, String),
    /// Set of binary operator function names that are FFI builtins (as dict)
    ffi_binary_ops: dict.Dict(String, Bool),
    /// Set of unary operator function names that are FFI builtins (as dict)
    ffi_unary_ops: dict.Dict(String, Bool),
    /// Registry of primitive types and their Core AST representations
    primitive_types: PrimitiveTypes,
  )
}

// ============================================================================
// OPERATOR MAPPING HELPERS
// ============================================================================

/// Get the function name for a binary operator token.
/// Returns the function name the operator should desugar to.
pub fn binary_op_name(config: LanguageConfig, op: String) -> Option(String) {
  case dict.get(config.binary_ops, op) {
    Ok(name) -> Some(name)
    Error(Nil) -> None
  }
}

/// Get the function name for a unary operator token.
/// Returns the function name the operator should desugar to.
pub fn unary_op_name(config: LanguageConfig, op: String) -> Option(String) {
  case dict.get(config.unary_ops, op) {
    Ok(name) -> Some(name)
    Error(Nil) -> None
  }
}

/// Check if a binary operator is an FFI builtin.
pub fn is_ffi_binary_op(config: LanguageConfig, op: String) -> Bool {
  case dict.get(config.ffi_binary_ops, op) {
    Ok(True) -> True
    Ok(False) -> False
    Error(Nil) -> False
  }
}

/// Check if a unary operator is an FFI builtin.
pub fn is_ffi_unary_op(config: LanguageConfig, op: String) -> Bool {
  case dict.get(config.ffi_unary_ops, op) {
    Ok(True) -> True
    Ok(False) -> False
    Error(Nil) -> False
  }
}

// ============================================================================
// PRIMITIVE TYPES
// ============================================================================

/// Registry of primitive types and their Core AST representations.
pub type PrimitiveTypes {
  PrimitiveTypes(
    /// Mapping from name (e.g., "I32") to Core literal type
    types: List(#(String, core_ast.LiteralType)),
  )
}

/// Look up the Core literal type for a name.
pub fn lookup_primitive_type(ptypes: PrimitiveTypes, name: String) -> Option(core_ast.LiteralType) {
  case list.find(ptypes.types, fn(pair) { pair.0 == name }) {
    Ok(typ) -> Some(typ.1)
    Error(Nil) -> None
  }
}

/// Get all primitive type names.
pub fn primitive_type_names(ptypes: PrimitiveTypes) -> List(String) {
  list.map(ptypes.types, fn(pair) { pair.0 })
}

/// Check if a name is a primitive type.
pub fn is_primitive_type(ptypes: PrimitiveTypes, name: String) -> Bool {
  list.any(ptypes.types, fn(pair) { pair.0 == name })
}

// ============================================================================
// TAO DEFAULT CONFIGURATION
// ============================================================================

/// Create the default configuration for the Tao language.
pub fn default_config() -> LanguageConfig {
  LanguageConfig(
    truth_constructor: "True",
    false_constructor: "False",
    bool_type: "Bool",
    list_cons: "Cons",
    list_nil: "Nil",
    binary_ops: dict.from_list([
      #("+", "add"), #("-", "sub"), #("*", "mul"), #("/", "div"),
      #("%", "mod"), #("==", "eq"), #("/=", "neq"), #("<", "lt"),
      #(">", "gt"), #("<=", "lte"), #(">=", "gte"), #("and", "and"),
      #("or", "or"), #("++", "concat"), #("|>", "pipe"),
    ]),
    unary_ops: dict.from_list([
      #("-", "negate"), #("not", "not"),
    ]),
    ffi_binary_ops: dict.from_list([
      #("add", True), #("sub", True), #("mul", True), #("div", True),
      #("eq", True), #("neq", True), #("lt", True), #("gt", True),
      #("lte", True), #("gte", True),
    ]),
    ffi_unary_ops: dict.from_list([#("negate", True)]),
    primitive_types: default_primitive_types(),
  )
}

/// Create the default primitive types registry.
pub fn default_primitive_types() -> PrimitiveTypes {
  PrimitiveTypes([
    #("I32", core_ast.I32T),
    #("I64", core_ast.I64T),
    #("U32", core_ast.U32T),
    #("U64", core_ast.U64T),
    #("F32", core_ast.F32T),
    #("F64", core_ast.F64T),
  ])
}

/// Convert the bool_type string from LanguageConfig to a Core type reference.
/// Used by the FFI layer to specify the return type of comparison operators.
pub fn bool_type_as_core(config: LanguageConfig) -> core_ast.Type {
  // Create a type reference to the Bool constructor: VCtrValue(VCtr("Bool", VUnit))
  core_ast.VCtrValue(core_ast.VCtr(config.bool_type, core_ast.VUnit))
}
