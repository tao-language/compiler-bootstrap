// ============================================================================
// CORE LANGUAGE SYNTAX TESTS
// ============================================================================
/// Round-trip tests for the core language syntax (parser and formatter).
///
/// Each test follows this pattern:
/// 1. Parse source to AST
/// 2. Verify AST structure
/// 3. Format AST back to source
/// 4. Verify formatted source matches expected
///
/// Syntax reference:
/// - Variables: `x`
/// - Literals: `42`
/// - Lambda: `x -> body`
/// - Pi types: `(x : A) -> B`
/// - Application: `f(x)`
/// - Type annotations: `x : %I32`
/// - Field access: `record.field`
/// - Records: `{}`
/// - Constructors: `#True`, `#Some`, `#Maybe(a)`
/// - Type universes: `%Type`, `%Type(1)`
/// - Holes: `?`, `?1`, `?2`
/// - Literal types: `%I32`, `%I64`, `%F64`
import core/syntax
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// VARIABLE TESTS
// ============================================================================

pub fn roundtrip_var_test() {
  // Free variables format as var0 (De Bruijn index with no binding in scope)
  let source = "x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_var_underscore_test() {
  // Underscore is a wildcard pattern, not a standalone expression
  // It's only valid in pattern contexts (match clauses, lambda patterns)
  // This test verifies that underscore alone is NOT a valid expression
  let source = "_"
  let result = syntax.parse(source)
  // Underscore alone is not a valid expression - it's a pattern
  result.errors |> should.not_equal([])
}

// ============================================================================
// LITERAL TESTS
// ============================================================================

pub fn roundtrip_lit_zero_test() {
  let source = "0"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_lit_positive_test() {
  let source = "42"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// LAMBDA TESTS
// ============================================================================

pub fn roundtrip_lambda_simple_test() {
  let source = "x -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  // Verify round-trip: parse then format should give same source
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%fn(x) -> x")
}

pub fn roundtrip_lambda_different_var_test() {
  let source = "y -> y"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%fn(y) -> y")
}

pub fn roundtrip_lambda_nested_test() {
  let source = "x -> y -> y"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%fn(x) -> %fn(y) -> y")
}

pub fn roundtrip_lambda_shadowing_test() {
  // This tests that variable shadowing works correctly
  // x -> y -> x should preserve the reference to outer x
  let source = "x -> y -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%fn(x) -> %fn(y) -> x")
}

pub fn roundtrip_lambda_self_shadowing_test() {
  // x -> x -> x should show shadowing: inner x shadows outer x
  // The innermost x refers to the middle lambda's parameter
  let source = "x -> x -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  // The inner x refers to the middle lambda's x (var0)
  // The middle x refers to the outer lambda's x (var1)
  formatted |> should.equal("%fn(x) -> %fn(x) -> x")
}

// ============================================================================
// PI TYPE TESTS
// ============================================================================

pub fn roundtrip_pi_simple_test() {
  let source = "(x : %I32) -> %I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%pi(x : %I32) -> %I32")
}

pub fn roundtrip_pi_with_type_universe_test() {
  let source = "(x : %Type) -> %Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%pi(x : %Type) -> %Type")
}

pub fn roundtrip_pi_with_level_test() {
  let source = "(x : %Type(1)) -> %Type(1)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("%pi(x : %Type(1)) -> %Type(1)")
}

// ============================================================================
// APPLICATION TESTS
// ============================================================================

pub fn roundtrip_app_simple_test() {
  let source = "f(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0)")
}

pub fn roundtrip_app_with_literal_test() {
  let source = "f(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(42)")
}

pub fn roundtrip_app_nested_test() {
  let source = "f(g(x))"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0(var0))")
}

// ============================================================================
// TYPE ANNOTATION TESTS
// ============================================================================

pub fn roundtrip_annotation_simple_test() {
  let source = "x : %I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0 : %I32")
}

pub fn roundtrip_annotation_with_type_universe_test() {
  let source = "x : %Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0 : %Type")
}

// ============================================================================
// FIELD ACCESS TESTS
// ============================================================================

pub fn roundtrip_field_access_simple_test() {
  let source = "x.field"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0.field")
}

// ============================================================================
// CONSTRUCTOR TESTS
// ============================================================================

pub fn roundtrip_constructor_nullary_test() {
  let source = "#True"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_some_test() {
  let source = "#Some"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_none_test() {
  let source = "#None"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_with_arg_test() {
  let source = "#Some(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("#Some(var0)")
}

// ============================================================================
// TYPE UNIVERSE TESTS
// ============================================================================

pub fn roundtrip_type_universe_zero_test() {
  let source = "%Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_type_universe_one_test() {
  let source = "%Type(1)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_type_universe_two_test() {
  let source = "%Type(2)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// LITERAL TYPE TESTS
// ============================================================================

pub fn roundtrip_litt_i32_test() {
  let source = "%I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_i64_test() {
  let source = "%I64"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_f64_test() {
  let source = "%F64"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// HOLE TESTS
// ============================================================================

pub fn roundtrip_hole_simple_test() {
  let source = "?"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_hole_with_id_test() {
  let source = "?1"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_hole_with_id_two_test() {
  let source = "?2"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// RECORD TESTS
// ============================================================================

pub fn roundtrip_record_empty_test() {
  let source = "{}"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_record_single_field_test() {
  let source = "{x: 1}"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_record_multiple_fields_test() {
  let source = "{x: 1, y: 2, z: 3}"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// PARENTHESIS TESTS
// ============================================================================

pub fn roundtrip_parens_simple_test() {
  let source = "(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_parens_preserved_when_needed_test() {
  let source = "(x -> x)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("(%fn(x) -> x)(42)")
}

// ============================================================================
// COMPLEX EXPRESSION TESTS
// ============================================================================

pub fn roundtrip_lambda_in_app_test() {
  let source = "(x -> x)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("(%fn(x) -> x)(42)")
}

pub fn roundtrip_pi_in_app_test() {
  let source = "((x : %I32) -> %I32)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  // Formatter outputs new syntax
  formatted |> should.equal("(%pi(x : %I32) -> %I32)(42)")
}

pub fn roundtrip_annotation_in_app_test() {
  let source = "(x : %I32)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("(var0 : %I32)(42)")
}
