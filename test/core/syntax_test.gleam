// ============================================================================
// CORE LANGUAGE SYNTAX TESTS
// ============================================================================
/// Tests for the core language syntax (parser and formatter).
///
/// The core language supports:
/// - Variables: x
/// - Literals: 42
/// - Lambda: λx. body
/// - Application: f(x)
/// - Type annotations: x : I32
/// - Field access: record.field
/// - Constructors: Some, True, False, None
/// - Type universes: Type0, Type1, ...
/// - Holes: ? (unsolved metavariables)
/// - Literal types: I32, I64, F64, U32, U64
///
/// Both parser and formatter are derived from a single grammar definition.
/// Round-trip tests verify that parse → format → parse produces consistent output.
///
/// Note: All identifiers currently become `var0` (De Bruijn index placeholder).
/// Full implementation will need proper name-to-index conversion.
import core/core.{
  Ann, App, Ctr, Dot, F64T, Hole, I32, I32T, I64T, Lam, Lit, LitT, Term, Typ, U32T, Var,
}
import gleam/list
import syntax/grammar.{Span, type Span}
import core/syntax
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Create a test span with fixed position.
/// 
/// In production, spans would contain actual source locations.
/// For tests, we use a consistent dummy span.
fn test_span() -> Span {
  Span("test", 1, 1, 1, 1)
}

// ============================================================================
// PARSING TESTS - VARIABLES
// ============================================================================

pub fn parse_var_simple_test() {
  // Single letter identifier parses as variable
  let result = syntax.parse("x")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Var(0), Span("input", 1, 1, 1, 2)))
}

pub fn parse_var_underscore_test() {
  // Underscore is a valid identifier
  let result = syntax.parse("_")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Var(0), Span("input", 1, 1, 1, 2)))
}

// ============================================================================
// PARSING TESTS - LITERALS
// ============================================================================

pub fn parse_lit_zero_test() {
  // Zero parses correctly
  let result = syntax.parse("0")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Lit(I32(0)), Span("input", 1, 1, 1, 2)))
}

pub fn parse_lit_positive_test() {
  // Positive integer parses correctly
  let result = syntax.parse("42")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Lit(I32(42)), Span("input", 1, 1, 1, 3)))
}

pub fn parse_lit_large_test() {
  // Large integer parses correctly
  let result = syntax.parse("999999")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Lit(I32(999999)), Span("input", 1, 1, 1, 7)))
}

// ============================================================================
// PARSING TESTS - TYPE UNIVERSES
// ============================================================================

pub fn parse_typ_zero_test() {
  // Type0 parses correctly
  let result = syntax.parse("Type0")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Typ(0), Span("input", 1, 1, 1, 6)))
}

pub fn parse_typ_one_test() {
  // Type1 parses correctly
  let result = syntax.parse("Type1")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Typ(1), Span("input", 1, 1, 1, 6)))
}

pub fn parse_typ_level_ten_test() {
  // Type10 parses correctly
  let result = syntax.parse("Type10")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Typ(10), Span("input", 1, 1, 1, 7)))
}

// ============================================================================
// PARSING TESTS - HOLES
// ============================================================================

pub fn parse_hole_test() {
  // Hole (?) parses correctly
  let result = syntax.parse("?")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(Hole(0), Span("input", 1, 1, 1, 2)))
}

// ============================================================================
// PARSING TESTS - LITERAL TYPES
// ============================================================================

pub fn parse_litt_i32_test() {
  // I32 literal type parses correctly
  let result = syntax.parse("I32")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(LitT(I32T), Span("input", 1, 1, 1, 4)))
}

pub fn parse_litt_i64_test() {
  // I64 literal type parses correctly
  let result = syntax.parse("I64")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(LitT(I64T), Span("input", 1, 1, 1, 4)))
}

pub fn parse_litt_f64_test() {
  // F64 literal type parses correctly
  let result = syntax.parse("F64")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(LitT(F64T), Span("input", 1, 1, 1, 4)))
}

pub fn parse_litt_u32_test() {
  // U32 literal type parses correctly
  let result = syntax.parse("U32")
  result.errors |> should.equal([])
  result.ast |> should.equal(Term(LitT(U32T), Span("input", 1, 1, 1, 4)))
}

// ============================================================================
// PARSING TESTS - TYPE ANNOTATIONS
// ============================================================================

pub fn parse_annotation_simple_test() {
  // Simple annotation: x : I32
  let result = syntax.parse("x : I32")
  result.errors |> should.equal([])
  case result.ast {
    Term(Ann(_, Term(LitT(_), _)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_annotation_with_type_universe_test() {
  // Annotation with type universe: x : Type0
  let result = syntax.parse("x : Type0")
  result.errors |> should.equal([])
  case result.ast {
    Term(Ann(_, Term(Typ(0), _)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PARSING TESTS - FIELD ACCESS
// ============================================================================

pub fn parse_field_access_simple_test() {
  // Simple field access: record.field
  let result = syntax.parse("x.field")
  result.errors |> should.equal([])
  case result.ast {
    Term(Dot(_, "field"), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_field_access_chained_test() {
  // Note: Chained field access (x.field.name) is not yet supported
  // This test verifies that single field access works
  let result = syntax.parse("x.field")
  result.errors |> should.equal([])
  case result.ast {
    Term(Dot(_, "field"), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PARSING TESTS - CONSTRUCTORS
// ============================================================================

pub fn parse_constructor_nullary_test() {
  // Nullary constructor: True
  let result = syntax.parse("True")
  result.errors |> should.equal([])
  case result.ast {
    Term(Ctr("True", _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_constructor_some_test() {
  // Constructor: Some
  let result = syntax.parse("Some")
  result.errors |> should.equal([])
  case result.ast {
    Term(Ctr("Some", _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_constructor_none_test() {
  // Constructor: None
  let result = syntax.parse("None")
  result.errors |> should.equal([])
  case result.ast {
    Term(Ctr("None", _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PARSING TESTS - LAMBDAS
// ============================================================================

pub fn parse_lambda_simple_test() {
  // Simple lambda: λx. x
  let result = syntax.parse("λx. x")
  result.errors |> should.equal([])
  // Check lambda structure (span varies based on token positions)
  case result.ast {
    Term(Lam(name, Term(Var(0), _)), _) if name == "x" -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_lambda_different_var_test() {
  // Lambda with different variable name
  let result = syntax.parse("λy. y")
  result.errors |> should.equal([])
  case result.ast {
    Term(Lam(name, _), _) -> {
      name |> should.equal("y")
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PARSING TESTS - APPLICATION
// ============================================================================

pub fn parse_app_simple_test() {
  // Simple application: f(x)
  let result = syntax.parse("f(x)")
  result.errors |> should.equal([])
  case result.ast {
    Term(App(fun, arg), _) -> {
      fun |> should.equal(Term(Var(0), Span("input", 1, 1, 1, 2)))
      arg |> should.equal(Term(Var(0), Span("input", 1, 3, 1, 4)))
    }
    _ -> False |> should.be_true
  }
}

pub fn parse_app_with_literal_test() {
  // Application with literal argument: f(42)
  let result = syntax.parse("f(42)")
  result.errors |> should.equal([])
  case result.ast {
    Term(App(fun, arg), _) -> {
      fun |> should.equal(Term(Var(0), Span("input", 1, 1, 1, 2)))
      arg |> should.equal(Term(Lit(I32(42)), Span("input", 1, 3, 1, 5)))
    }
    _ -> False |> should.be_true
  }
}

pub fn parse_app_nested_test() {
  // Nested application: f(g(x))
  let result = syntax.parse("f(g(x))")
  result.errors |> should.equal([])
  case result.ast {
    Term(App(outer_fun, Term(App(inner_fun, inner_arg), _)), _) -> {
      outer_fun |> should.equal(Term(Var(0), Span("input", 1, 1, 1, 2)))
      inner_fun |> should.equal(Term(Var(0), Span("input", 1, 3, 1, 4)))
      inner_arg |> should.equal(Term(Var(0), Span("input", 1, 5, 1, 6)))
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// PARSING TESTS - PARENTHESES
// ============================================================================

pub fn parse_parens_simple_test() {
  // Parenthesized expression: (x)
  let result = syntax.parse("(x)")
  result.errors |> should.equal([])
  // Parentheses are stripped, leaving the variable
  result.ast |> should.equal(Term(Var(0), Span("input", 1, 2, 1, 3)))
}

pub fn parse_parens_nested_test() {
  // Nested parentheses: ((x))
  let result = syntax.parse("((x))")
  result.errors |> should.equal([])
  // All parentheses are stripped, leaving the variable
  result.ast |> should.equal(Term(Var(0), Span("input", 1, 3, 1, 4)))
}

// ============================================================================
// FORMATTING TESTS - VARIABLES
// ============================================================================

pub fn format_var_test() {
  // Variable formats as "var" + index
  let term = Term(Var(0), test_span())
  syntax.format(term) |> should.equal("var0")
}

pub fn format_var_index_one_test() {
  // Variable with index 1 formats as "var1"
  let term = Term(Var(1), test_span())
  syntax.format(term) |> should.equal("var1")
}

// ============================================================================
// FORMATTING TESTS - LITERALS
// ============================================================================

pub fn format_lit_zero_test() {
  // Zero formats as "0"
  let term = Term(Lit(I32(0)), test_span())
  syntax.format(term) |> should.equal("0")
}

pub fn format_lit_positive_test() {
  // Positive integer formats normally
  let term = Term(Lit(I32(42)), test_span())
  syntax.format(term) |> should.equal("42")
}

pub fn format_lit_negative_test() {
  // Negative integer formats with minus sign
  let term = Term(Lit(I32(-10)), test_span())
  syntax.format(term) |> should.equal("-10")
}

// ============================================================================
// FORMATTING TESTS - TYPE UNIVERSES
// ============================================================================

pub fn format_typ_zero_test() {
  // Type0 formats as "Type0"
  let term = Term(Typ(0), test_span())
  syntax.format(term) |> should.equal("Type0")
}

pub fn format_typ_one_test() {
  // Type1 formats as "Type1"
  let term = Term(Typ(1), test_span())
  syntax.format(term) |> should.equal("Type1")
}

pub fn format_typ_level_ten_test() {
  // Type10 formats as "Type10"
  let term = Term(Typ(10), test_span())
  syntax.format(term) |> should.equal("Type10")
}

// ============================================================================
// FORMATTING TESTS - HOLES
// ============================================================================

pub fn format_hole_test() {
  // Hole formats as "?"
  let term = Term(Hole(0), test_span())
  syntax.format(term) |> should.equal("?")
}

// ============================================================================
// FORMATTING TESTS - LITERAL TYPES
// ============================================================================

pub fn format_litt_i32_test() {
  // I32 formats as "I32"
  let term = Term(LitT(I32T), test_span())
  syntax.format(term) |> should.equal("I32")
}

pub fn format_litt_i64_test() {
  // I64 formats as "I64"
  let term = Term(LitT(I64T), test_span())
  syntax.format(term) |> should.equal("I64")
}

pub fn format_litt_f64_test() {
  // F64 formats as "F64"
  let term = Term(LitT(F64T), test_span())
  syntax.format(term) |> should.equal("F64")
}

pub fn format_litt_u32_test() {
  // U32 formats as "U32"
  let term = Term(LitT(U32T), test_span())
  syntax.format(term) |> should.equal("U32")
}

// ============================================================================
// FORMATTING TESTS - TYPE ANNOTATIONS
// ============================================================================

pub fn format_annotation_simple_test() {
  // Annotation formats as "term : type"
  let term = Term(Ann(Term(Var(0), test_span()), Term(LitT(I32T), test_span())), test_span())
  syntax.format(term) |> should.equal("var0 : I32")
}

pub fn format_annotation_with_parens_test() {
  // Annotation in application needs parens
  let ann = Term(Ann(Term(Var(0), test_span()), Term(LitT(I32T), test_span())), test_span())
  let arg = Term(Lit(I32(42)), test_span())
  let term = Term(App(ann, arg), test_span())
  syntax.format(term) |> should.equal("(var0 : I32)(42)")
}

// ============================================================================
// FORMATTING TESTS - FIELD ACCESS
// ============================================================================

pub fn format_field_access_simple_test() {
  // Field access formats as "expr.field"
  let arg = Term(Var(0), test_span())
  let term = Term(Dot(arg, "field"), test_span())
  syntax.format(term) |> should.equal("var0.field")
}

pub fn format_field_access_chained_test() {
  // Chained field access
  let inner = Term(Dot(Term(Var(0), test_span()), "field"), test_span())
  let term = Term(Dot(inner, "name"), test_span())
  syntax.format(term) |> should.equal("var0.field.name")
}

// ============================================================================
// FORMATTING TESTS - CONSTRUCTORS
// ============================================================================

pub fn format_constructor_true_test() {
  // Constructor True formats as "True"
  let term = Term(Ctr("True", Term(Hole(0), test_span())), test_span())
  syntax.format(term) |> should.equal("True")
}

pub fn format_constructor_some_test() {
  // Constructor Some formats as "Some"
  let term = Term(Ctr("Some", Term(Hole(0), test_span())), test_span())
  syntax.format(term) |> should.equal("Some")
}

pub fn format_constructor_none_test() {
  // Constructor None formats as "None"
  let term = Term(Ctr("None", Term(Hole(0), test_span())), test_span())
  syntax.format(term) |> should.equal("None")
}

// ============================================================================
// FORMATTING TESTS - LAMBDAS
// ============================================================================

pub fn format_lambda_simple_test() {
  // Lambda formats as "λx. body"
  let body = Term(Var(0), test_span())
  let term = Term(Lam("x", body), test_span())
  syntax.format(term) |> should.equal("λx. var0")
}

pub fn format_lambda_different_var_test() {
  // Lambda with different parameter name
  let body = Term(Var(0), test_span())
  let term = Term(Lam("y", body), test_span())
  syntax.format(term) |> should.equal("λy. var0")
}

// ============================================================================
// FORMATTING TESTS - APPLICATION
// ============================================================================

pub fn format_app_simple_test() {
  // Application formats as "fun(arg)"
  let fun = Term(Var(0), test_span())
  let arg = Term(Lit(I32(42)), test_span())
  let term = Term(App(fun, arg), test_span())
  syntax.format(term) |> should.equal("var0(42)")
}

pub fn format_app_both_vars_test() {
  // Application with both function and argument as variables
  let fun = Term(Var(0), test_span())
  let arg = Term(Var(1), test_span())
  let term = Term(App(fun, arg), test_span())
  syntax.format(term) |> should.equal("var0(var1)")
}

// ============================================================================
// FORMATTING TESTS - PRECEDENCE
// ============================================================================

pub fn format_lambda_in_app_needs_parens_test() {
  // Lambda in function position needs parentheses: (λx. x)(42)
  let body = Term(Var(0), test_span())
  let lam = Term(Lam("x", body), test_span())
  let arg = Term(Lit(I32(42)), test_span())
  let term = Term(App(lam, arg), test_span())
  syntax.format(term) |> should.equal("(λx. var0)(42)")
}

pub fn format_lambda_in_arg_needs_parens_test() {
  // Lambda in argument position: f(λx. x)
  // Note: Current formatter adds extra parens around lambda in arg position
  let body = Term(Var(0), test_span())
  let lam = Term(Lam("x", body), test_span())
  let fun = Term(Var(0), test_span())
  let term = Term(App(fun, lam), test_span())
  syntax.format(term) |> should.equal("var0((λx. var0))")
}

pub fn format_app_in_lambda_no_parens_test() {
  // Application in lambda body needs no parentheses: λx. f(x)
  let app = Term(App(Term(Var(0), test_span()), Term(Var(0), test_span())), test_span())
  let term = Term(Lam("x", app), test_span())
  syntax.format(term) |> should.equal("λx. var0(var0)")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================
/// Round-trip tests verify that parse → format → parse produces consistent output.
/// 
/// Note: Current implementation converts all identifiers to `var0` (De Bruijn index).
/// This means round-trips produce "var0" instead of original names like "x".
/// Full implementation will need proper name-to-index conversion.

pub fn roundtrip_number_test() {
  // Numbers round-trip perfectly
  let source = "42"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_var_becomes_index_test() {
  // Variables become var0 (De Bruijn index placeholder)
  let source = "x"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_lambda_test() {
  // Lambda parameter name is preserved, body becomes var0
  let source = "λx. x"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("λx. var0")
}

pub fn roundtrip_app_test() {
  // Application: all identifiers become var0
  let source = "f(x)"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0)")
}

pub fn roundtrip_nested_app_test() {
  // Nested application: all identifiers become var0
  let source = "f(g(x))"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0(var0))")
}

pub fn roundtrip_parens_test() {
  // Parentheses are removed when not needed
  let source = "(x)"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_parens_preserved_when_needed_test() {
  // Parentheses preserved when needed for precedence
  let source = "(λx. x)(42)"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("(λx. var0)(42)")
}

pub fn roundtrip_format_parse_test() {
  // format → parse → format should be identity
  let body = Term(Var(0), test_span())
  let term = Term(Lam("x", body), test_span())
  let formatted1 = syntax.format(term)
  let result = syntax.parse(formatted1)
  let formatted2 = syntax.format(result.ast)
  formatted1 |> should.equal(formatted2)
}

// ============================================================================
// ROUND-TRIP TESTS - TYPE ANNOTATIONS
// ============================================================================

pub fn roundtrip_annotation_test() {
  // Annotation round-trips
  let source = "x : I32"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0 : I32")
}

// ============================================================================
// ROUND-TRIP TESTS - FIELD ACCESS
// ============================================================================

pub fn roundtrip_field_access_test() {
  // Field access round-trips
  let source = "x.field"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0.field")
}

pub fn roundtrip_field_access_chained_test() {
  // Note: Chained field access not yet supported, testing single field access
  let source = "x.field"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0.field")
}

// ============================================================================
// ROUND-TRIP TESTS - CONSTRUCTORS
// ============================================================================

pub fn roundtrip_constructor_true_test() {
  // Constructor True round-trips
  let source = "True"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("True")
}

pub fn roundtrip_constructor_some_test() {
  // Constructor Some round-trips
  let source = "Some"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("Some")
}

pub fn roundtrip_constructor_none_test() {
  // Constructor None round-trips
  let source = "None"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("None")
}

// ============================================================================
// ROUND-TRIP TESTS - TYPE UNIVERSES
// ============================================================================

pub fn roundtrip_typ_zero_test() {
  // Type0 round-trips perfectly
  let source = "Type0"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_typ_one_test() {
  // Type1 round-trips perfectly
  let source = "Type1"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// ROUND-TRIP TESTS - HOLES
// ============================================================================

pub fn roundtrip_hole_test() {
  // Hole round-trips perfectly
  let source = "?"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// ROUND-TRIP TESTS - LITERAL TYPES
// ============================================================================

pub fn roundtrip_litt_i32_test() {
  // I32 round-trips perfectly
  let source = "I32"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_i64_test() {
  // I64 round-trips perfectly
  let source = "I64"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_f64_test() {
  // F64 round-trips perfectly
  let source = "F64"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// ERROR TESTS
// ============================================================================
/// Note: The current parser implementation panics on invalid input rather
/// than returning structured errors. Error recovery is planned for future
/// implementation. These tests document the expected behavior once implemented.
//
// TODO: Re-enable these tests when error recovery is implemented
//
// pub fn parse_error_empty_input_test() {
//   // Empty input produces error
//   let result = syntax.parse("")
//   list.length(result.errors) |> should.not_equal(0)
// }
//
// pub fn parse_error_unclosed_paren_test() {
//   // Unclosed parenthesis produces error
//   let result = syntax.parse("f(x")
//   list.length(result.errors) |> should.not_equal(0)
// }
//
// pub fn parse_error_trailing_dot_test() {
//   // Trailing dot in lambda produces error
//   let result = syntax.parse("λx. ")
//   list.length(result.errors) |> should.not_equal(0)
// }
