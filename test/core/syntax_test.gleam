// ============================================================================
// CORE LANGUAGE SYNTAX TESTS
// ============================================================================
import core/core.{App, I32, Lam, Lit, Span, Term, Var}
import core/syntax
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// PARSING TESTS
// ============================================================================

pub fn parse_var_test() {
  let result = syntax.parse("x")
  result.errors |> should.equal([])
}

pub fn parse_number_test() {
  let result = syntax.parse("42")
  result.errors |> should.equal([])
  case result.ast {
    Term(Lit(I32(n)), _) -> n |> should.equal(42)
    _ -> False |> should.be_true
  }
}

pub fn parse_lambda_test() {
  let result = syntax.parse("λx. x")
  result.errors |> should.equal([])
  case result.ast {
    Term(Lam(_, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_app_test() {
  let result = syntax.parse("f(x)")
  result.errors |> should.equal([])
  case result.ast {
    Term(App(_, _), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn parse_nested_app_test() {
  let result = syntax.parse("f(g(x))")
  result.errors |> should.equal([])
}

pub fn parse_parens_test() {
  let result = syntax.parse("(x)")
  result.errors |> should.equal([])
}

// ============================================================================
// FORMATTING TESTS
// ============================================================================

pub fn format_var_test() {
  let term = Term(Var(0), span())
  syntax.format(term) |> should.equal("var0")
}

pub fn format_lit_test() {
  let term = Term(Lit(I32(42)), span())
  syntax.format(term) |> should.equal("42")
}

pub fn format_lambda_test() {
  let body = Term(Var(0), span())
  let term = Term(Lam("x", body), span())
  syntax.format(term) |> should.equal("λx. var0")
}

pub fn format_app_test() {
  let fun = Term(Var(0), span())
  let arg = Term(Lit(I32(42)), span())
  let term = Term(App(fun, arg), span())
  syntax.format(term) |> should.equal("var0(42)")
}

// ============================================================================
// ROUND-TRIP TESTS
// Note: These tests show current behavior where identifiers are converted
// to De Bruijn indices (Var(0)), so round-trip produces "var0" instead of "x".
// Full implementation will need proper name-to-index conversion.
// ============================================================================

pub fn roundtrip_var_test() {
  let source = "x"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  // Identifier becomes var0 (De Bruijn index)
  formatted |> should.equal("var0")
}

pub fn roundtrip_number_test() {
  let source = "42"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_lambda_test() {
  let source = "λx. x"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  // Parameter name is preserved, body becomes var0
  formatted |> should.equal("λx. var0")
}

pub fn roundtrip_app_test() {
  let source = "f(x)"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  // Identifiers become var0
  formatted |> should.equal("var0(var0)")
}

pub fn roundtrip_nested_app_test() {
  let source = "f(g(x))"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0(var0))")
}

pub fn roundtrip_parens_test() {
  let source = "(x)"
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

// ============================================================================
// PRECEDENCE TESTS
// ============================================================================

pub fn format_lambda_in_app_test() {
  // (λx. x)(42) - lambda in application needs parens
  let body = Term(Var(0), span())
  let lam = Term(Lam("x", body), span())
  let arg = Term(Lit(I32(42)), span())
  let term = Term(App(lam, arg), span())
  syntax.format(term) |> should.equal("(λx. var0)(42)")
}

pub fn format_app_in_lambda_test() {
  // λx. f(x) - no parens needed
  let app = Term(App(Term(Var(0), span()), Term(Var(0), span())), span())
  let term = Term(Lam("x", app), span())
  syntax.format(term) |> should.equal("λx. var0(var0)")
}

// ============================================================================
// HELPERS
// ============================================================================

fn span() {
  Span("test", 0, 0)
}
