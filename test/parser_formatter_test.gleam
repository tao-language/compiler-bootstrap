// ============================================================================
// PARSER AND FORMATTER TESTS
// ============================================================================
/// Tests for the parser and formatter modules.

import core
import formatter
import gleeunit
import gleeunit/should
import parser

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LEXER TESTS
// ============================================================================

/// Test tokenizing source code
pub fn tokenize_test() {
  parser.tokenize("x") |> should.equal([parser.TokIdent("x"), parser.TokEOF])
  parser.tokenize("42") |> should.equal([parser.TokInteger(42), parser.TokEOF])
  parser.tokenize("Type") |> should.equal([parser.TokType(0), parser.TokEOF])
  parser.tokenize("=>") |> should.equal([parser.TokArrow, parser.TokEOF])
}

// ============================================================================
// PARSER TESTS
// ============================================================================

/// Test parsing various constructs
pub fn parse_test() {
  parser.parse_source("Type")
  |> should.equal(Ok(core.Term(core.Typ(0), core.Span("parsed", 0, 0))))
  
  parser.parse_source("42")
  |> should.equal(Ok(core.Term(core.Lit(core.I32(42)), core.Span("parsed", 0, 0))))
  
  parser.parse_source("?")
  |> should.equal(Ok(core.Term(core.Hole(0), core.Span("parsed", 0, 0))))
  
  parser.parse_source("{ x: 1 }")
  |> should.be_ok
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

/// Test formatting various constructs
pub fn format_test() {
  formatter.format(core.Term(core.Typ(0), core.Span("test", 0, 0)))
  |> should.equal("Type")
  
  formatter.format(core.Term(core.Lit(core.I32(42)), core.Span("test", 0, 0)))
  |> should.equal("42")
  
  formatter.format(core.Term(core.Hole(0), core.Span("test", 0, 0)))
  |> should.equal("?")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

/// Test that parsing and formatting are inverses
pub fn roundtrip_test() {
  let source = "Type"
  case parser.parse_source(source) {
    Ok(term) -> formatter.format(term) |> should.equal(source)
    Error(_) -> False |> should.be_true
  }
  
  let source = "42"
  case parser.parse_source(source) {
    Ok(term) -> formatter.format(term) |> should.equal(source)
    Error(_) -> False |> should.be_true
  }
}
