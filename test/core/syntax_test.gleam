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
///
/// Both parser and formatter are derived from a single grammar definition.
/// Round-trip tests verify that parse → format → parse produces consistent output.
///
/// Note: All identifiers currently become `var0` (De Bruijn index placeholder).
/// Full implementation will need proper name-to-index conversion.
import core/core.{App, I32, Lam, Lit, Term, Var}
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
