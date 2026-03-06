// ============================================================================
// CORE LANGUAGE PARSER AND FORMATTER TESTS
// ============================================================================
/// Comprehensive tests for the core language parser and formatter.

import core/parser as parser
import core/formatter as formatter
import core/core as core
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LEXER TESTS
// ============================================================================

/// Test tokenizing identifiers
pub fn tokenize_ident_test() {
  parser.tokenize("x") |> should.equal([parser.Ident("x"), parser.Hole])
  parser.tokenize("foo") |> should.equal([parser.Ident("foo"), parser.Hole])
  parser.tokenize("foo123") |> should.equal([parser.Ident("foo123"), parser.Hole])
}

/// Test tokenizing constructors
pub fn tokenize_constructor_test() {
  parser.tokenize("Cons") |> should.equal([parser.Constructor("Cons"), parser.Hole])
  parser.tokenize("Nil") |> should.equal([parser.Constructor("Nil"), parser.Hole])
  parser.tokenize("True") |> should.equal([parser.Constructor("True"), parser.Hole])
}

/// Test tokenizing integers
pub fn tokenize_integer_test() {
  parser.tokenize("42") |> should.equal([parser.Integer(42), parser.Hole])
  parser.tokenize("0") |> should.equal([parser.Integer(0), parser.Hole])
  parser.tokenize("123") |> should.equal([parser.Integer(123), parser.Hole])
}

/// Test tokenizing type keywords
pub fn tokenize_type_test() {
  parser.tokenize("Type") |> should.equal([parser.TypeKeyword(0), parser.Hole])
  parser.tokenize("Type0") |> should.equal([parser.TypeKeyword(0), parser.Hole])
  parser.tokenize("Type1") |> should.equal([parser.TypeKeyword(1), parser.Hole])
}

/// Test tokenizing literal types

/// Test tokenizing keywords
pub fn tokenize_keywords_test() {
  parser.tokenize("match") |> should.equal([parser.Match, parser.Hole])
  parser.tokenize("with") |> should.equal([parser.With, parser.Hole])
}

/// Test tokenizing punctuation
pub fn tokenize_punctuation_test() {
  parser.tokenize("=>") |> should.equal([parser.Arrow, parser.Hole])
  parser.tokenize(":") |> should.equal([parser.Colon, parser.Hole])
  parser.tokenize("(") |> should.equal([parser.LParen, parser.Hole])
  parser.tokenize(")") |> should.equal([parser.RParen, parser.Hole])
  parser.tokenize("{") |> should.equal([parser.LBrace, parser.Hole])
  parser.tokenize("}") |> should.equal([parser.RBrace, parser.Hole])
  parser.tokenize(",") |> should.equal([parser.Comma, parser.Hole])
  parser.tokenize("_") |> should.equal([parser.Underscore, parser.Hole])
  parser.tokenize("?") |> should.equal([parser.Hole, parser.Hole])
}

/// Test tokenizing whitespace
pub fn tokenize_whitespace_test() {
  parser.tokenize("  x  ") |> should.equal([parser.Ident("x"), parser.Hole])
  parser.tokenize("\n\nx\n\n") |> should.equal([parser.Ident("x"), parser.Hole])
  parser.tokenize("\tx\t") |> should.equal([parser.Ident("x"), parser.Hole])
}

/// Test tokenizing comments
pub fn tokenize_comment_test() {
  parser.tokenize("// comment\nx") |> should.equal([parser.Ident("x"), parser.Hole])
  parser.tokenize("x // comment") |> should.equal([parser.Ident("x"), parser.Hole])
}

// ============================================================================
// PARSER TESTS
// ============================================================================

/// Test parsing type
pub fn parse_type_test() {
  parser.parse_source("Type")
  |> should.equal(Ok(core.Term(core.Typ(0), core.Span("parsed", 0, 0))))
  
  parser.parse_source("Type1")
  |> should.equal(Ok(core.Term(core.Typ(1), core.Span("parsed", 0, 0))))
}

/// Test parsing literal type

/// Test parsing integer literal
pub fn parse_literal_test() {
  parser.parse_source("42")
  |> should.equal(Ok(core.Term(core.Lit(core.I32(42)), core.Span("parsed", 0, 0))))
  
  parser.parse_source("0")
  |> should.equal(Ok(core.Term(core.Lit(core.I32(0)), core.Span("parsed", 0, 0))))
}

/// Test parsing hole
pub fn parse_hole_test() {
  parser.parse_source("?")
  |> should.equal(Ok(core.Term(core.Hole(0), core.Span("parsed", 0, 0))))
}

/// Test parsing variable
pub fn parse_variable_test() {
  parser.parse_source("x")
  |> should.be_ok
}

/// Test parsing lambda
pub fn parse_lambda_test() {
  parser.parse_source("(x: Type) => x")
  |> should.be_ok
}

/// Test parsing application
pub fn parse_application_test() {
  parser.parse_source("f(x)")
  |> should.be_ok
}

/// Test parsing record
pub fn parse_record_test() {
  parser.parse_source("{ x: 1 }")
  |> should.be_ok
  
  parser.parse_source("{ x: 1, y: 2 }")
  |> should.be_ok
}

/// Test parsing empty record
pub fn parse_empty_record_test() {
  parser.parse_source("{ }")
  |> should.be_ok
}

/// Test parsing constructor

/// Test parsing annotated term

/// Test parsing match expression

/// Test parsing nested expressions
pub fn parse_nested_test() {
  parser.parse_source("(x: Type) => f(x)")
  |> should.be_ok
  
  parser.parse_source("f(g(x))")
  |> should.be_ok
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

/// Test formatting type
pub fn format_type_test() {
  formatter.format(core.Term(core.Typ(0), core.Span("test", 0, 0)))
  |> should.equal("Type")
  
  formatter.format(core.Term(core.Typ(1), core.Span("test", 0, 0)))
  |> should.equal("Type1")
}

/// Test formatting literal type
pub fn format_literal_type_test() {
  formatter.format(core.Term(core.LitT(core.I32T), core.Span("test", 0, 0)))
  |> should.equal("I32")
  
  formatter.format(core.Term(core.LitT(core.F64T), core.Span("test", 0, 0)))
  |> should.equal("F64")
}

/// Test formatting literal
pub fn format_literal_test() {
  formatter.format(core.Term(core.Lit(core.I32(42)), core.Span("test", 0, 0)))
  |> should.equal("42")
  
  formatter.format(core.Term(core.Lit(core.I32(0)), core.Span("test", 0, 0)))
  |> should.equal("0")
}

/// Test formatting hole
pub fn format_hole_test() {
  formatter.format(core.Term(core.Hole(0), core.Span("test", 0, 0)))
  |> should.equal("?")
}

/// Test formatting variable
pub fn format_variable_test() {
  formatter.format(core.Term(core.Var(0), core.Span("test", 0, 0)))
  |> should.equal("x")
}

/// Test formatting lambda
pub fn format_lambda_test() {
  let body = core.Term(core.Var(0), core.Span("test", 0, 0))
  formatter.format(core.Term(core.Lam("x", body), core.Span("test", 0, 0)))
  |> should.equal("(x: A) => x")
}

/// Test formatting application
pub fn format_application_test() {
  let fun = core.Term(core.Var(0), core.Span("test", 0, 0))
  let arg = core.Term(core.Lit(core.I32(1)), core.Span("test", 0, 0))
  formatter.format(core.Term(core.App(fun, arg), core.Span("test", 0, 0)))
  |> should.equal("x(1)")
}

/// Test formatting record
pub fn format_record_test() {
  let fields = [#("x", core.Term(core.Lit(core.I32(1)), core.Span("test", 0, 0)))]
  formatter.format(core.Term(core.Rcd(fields), core.Span("test", 0, 0)))
  |> should.equal("{ x: 1 }")
}

/// Test formatting empty record
pub fn format_empty_record_test() {
  formatter.format(core.Term(core.Rcd([]), core.Span("test", 0, 0)))
  |> should.equal("{ }")
}

/// Test formatting constructor
pub fn format_constructor_test() {
  let arg = core.Term(core.Lit(core.I32(1)), core.Span("test", 0, 0))
  formatter.format(core.Term(core.Ctr("Cons", arg), core.Span("test", 0, 0)))
  |> should.equal("Cons(1)")
}

/// Test formatting annotation
pub fn format_annotation_test() {
  let term = core.Term(core.Var(0), core.Span("test", 0, 0))
  let typ = core.Term(core.Typ(0), core.Span("test", 0, 0))
  formatter.format(core.Term(core.Ann(term, typ), core.Span("test", 0, 0)))
  |> should.equal("(x: Type)")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

/// Test that parsing and formatting are inverses for types
pub fn roundtrip_type_test() {
  let source = "Type"
  case parser.parse_source(source) {
    Ok(term) -> formatter.format(term) |> should.equal(source)
    Error(_) -> False |> should.be_true
  }
}

/// Test that parsing and formatting are inverses for literals
pub fn roundtrip_literal_test() {
  let source = "42"
  case parser.parse_source(source) {
    Ok(term) -> formatter.format(term) |> should.equal(source)
    Error(_) -> False |> should.be_true
  }
}

/// Test that parsing and formatting are inverses for holes
pub fn roundtrip_hole_test() {
  let source = "?"
  case parser.parse_source(source) {
    Ok(term) -> formatter.format(term) |> should.equal(source)
    Error(_) -> False |> should.be_true
  }
}

/// Test that parsing and formatting are inverses for literal types

// ============================================================================
// PATTERN TESTS
// ============================================================================

/// Test formatting wildcard pattern
pub fn format_pattern_wildcard_test() {
  formatter.format_pattern(core.PAny)
  |> should.equal("_")
}

/// Test formatting variable pattern

/// Test formatting constructor pattern
pub fn format_pattern_constructor_test() {
  formatter.format_pattern(core.PCtr("Cons", core.PAny))
  |> should.equal("Cons(_)")
}
