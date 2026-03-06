// ============================================================================
// PARSER AND FORMATTER TESTS
// ============================================================================
/// Tests for the grammar, parser, and formatter modules.

import core
import formatter
import gleeunit
import gleeunit/should
import grammar
import parser
import gleam/list
import gleam/string

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LEXER TESTS
// ============================================================================

/// Test tokenizing identifiers
pub fn tokenize_identifier_test() {
  parser.tokenize("x") |> should.equal([parser.TokIdent("x"), parser.TokEOF])
  parser.tokenize("foo") |> should.equal([parser.TokIdent("foo"), parser.TokEOF])
}

/// Test tokenizing integers
pub fn tokenize_integer_test() {
  parser.tokenize("42") |> should.equal([parser.TokInteger(42), parser.TokEOF])
}

/// Test tokenizing Type keyword
pub fn tokenize_type_test() {
  parser.tokenize("Type") |> should.equal([parser.TokType(0), parser.TokEOF])
}

/// Test tokenizing punctuation
pub fn tokenize_punctuation_test() {
  parser.tokenize("=>") |> should.equal([parser.TokArrow, parser.TokEOF])
  parser.tokenize("(") |> should.equal([parser.TokLParen, parser.TokEOF])
  parser.tokenize("{") |> should.equal([parser.TokLBrace, parser.TokEOF])
}

// ============================================================================
// PARSER TESTS
// ============================================================================

/// Test parsing a type
pub fn parse_type_test() {
  parser.parse_source("Type")
  |> should.equal(Ok(core.Term(core.Typ(0), core.Span("parsed", 0, 0))))
}

/// Test parsing an integer literal
pub fn parse_literal_int_test() {
  parser.parse_source("42")
  |> should.equal(Ok(core.Term(core.Lit(core.I32(42)), core.Span("parsed", 0, 0))))
}

/// Test parsing a hole
pub fn parse_hole_test() {
  parser.parse_source("?")
  |> should.equal(Ok(core.Term(core.Hole(0), core.Span("parsed", 0, 0))))
}

/// Test parsing a record
pub fn parse_record_test() {
  parser.parse_source("{ x: 1 }")
  |> should.be_ok
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

/// Test formatting a type
pub fn format_type_test() {
  formatter.format(core.Term(core.Typ(0), core.Span("test", 0, 0)))
  |> should.equal("Type")
}

/// Test formatting a literal
pub fn format_literal_test() {
  formatter.format(core.Term(core.Lit(core.I32(42)), core.Span("test", 0, 0)))
  |> should.equal("42")
}

/// Test formatting a hole
pub fn format_hole_test() {
  formatter.format(core.Term(core.Hole(0), core.Span("test", 0, 0)))
  |> should.equal("?")
}

// ============================================================================
// GRAMMAR TESTS
// ============================================================================

/// Test creating a grammar
pub fn grammar_new_test() {
  let g = grammar.new("term")
  grammar.get_start_rule(g).name |> should.equal("term")
}

/// Test adding rules to grammar
pub fn grammar_rule_test() {
  let g =
    grammar.new("term")
    |> grammar.rule("atom", grammar.term("ident"))
  
  grammar.get_rule_names(g) |> list.length |> should.equal(1)
}

/// Test formatting a grammar
pub fn grammar_format_test() {
  let g =
    grammar.new("term")
    |> grammar.rule("term", grammar.ref_rule("atom"))
  
  grammar.format_grammar(g) |> string.contains("term") |> should.be_true
}
