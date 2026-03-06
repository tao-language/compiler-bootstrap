// ============================================================================
// PARSER TESTS
// ============================================================================

import gleam/list
import gleeunit
import gleeunit/should
import parser

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// LEXER TESTS
// ============================================================================

pub fn tokenize_ident_test() {
  let tokens = parser.tokenize("hello")
  tokens |> list.length |> should.equal(2)
}

pub fn tokenize_keyword_test() {
  let tokens = parser.tokenize("let")
  tokens |> list.length |> should.equal(2)
}

pub fn tokenize_int_test() {
  let tokens = parser.tokenize("42")
  tokens |> list.length |> should.equal(2)
}
