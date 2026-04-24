// Test runner - gleeunit finds all public functions ending in _test
import gleeunit
import syntax/lexer.{token_kinds}
import tao/desugar_test

pub fn main() {
  gleeunit.main()
}

pub fn test_lexer_tokenizes_keywords() {
  let source = "let x = 1 + 2"
  let kinds = token_kinds(lexer.tokenize(source, "test"))
  assert kinds == ["Keyword", "Identifier", "Identifier", "Number", "Operator", "Number"]
}

pub fn test_lexer_tokenizes_operators() {
  let source = "<- -> .."
  let kinds = token_kinds(lexer.tokenize(source, "test"))
  assert kinds == ["Operator", "Operator", "Operator"]
}

pub fn test_lexer_handles_strings() {
  let source = "hello world"
  let kinds = token_kinds(lexer.tokenize(source, "test"))
  assert kinds == ["String"]
}
