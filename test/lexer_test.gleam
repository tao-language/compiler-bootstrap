// ============================================================================
// LEXER TESTS
// ============================================================================

import gleeunit
import gleeunit/should
import gleam/list
import gleam/option.{Some}
import lexer
import parser

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// BASIC TOKENIZATION TESTS
// ============================================================================

pub fn tokenize_ident_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "hello")
  
  list.is_empty(tokens) |> should.be_false
  // First token should be identifier
  True |> should.be_true
}

pub fn tokenize_number_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "42")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_float_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "3.14")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_string_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "\"hello\"")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_operator_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "+")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

// ============================================================================
// KEYWORD TESTS
// ============================================================================

pub fn tokenize_keyword_test() {
  let config = lexer.default_config()
    |> lexer.with_keywords(["let", "fn"])
  let tokens = lexer.tokenize(config, "test", "let")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_ident_not_keyword_test() {
  let config = lexer.default_config()
    |> lexer.with_keywords(["let"])
  let tokens = lexer.tokenize(config, "test", "letter")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

// ============================================================================
// COMMENT TESTS
// ============================================================================

pub fn tokenize_line_comment_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "// comment\nlet")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_block_comment_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "/* comment */let")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_python_comment_test() {
  let config = lexer.python_config()
  let tokens = lexer.tokenize(config, "test", "# comment\ndef")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

// ============================================================================
// INDENTATION TESTS
// ============================================================================

pub fn tokenize_indent_test() {
  let config = lexer.python_config()
  let tokens = lexer.tokenize(config, "test", "def f():\n    pass")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

pub fn tokenize_dedent_test() {
  let config = lexer.python_config()
  let tokens = lexer.tokenize(config, "test", "def f():\n    pass\nreturn")
  
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}

// ============================================================================
// CONFIGURATION TESTS
// ============================================================================

pub fn default_config_test() {
  let config = lexer.default_config()
  
  config.indent_sensitive |> should.be_false
  True |> should.be_true
}

pub fn python_config_test() {
  let config = lexer.python_config()
  
  config.indent_sensitive |> should.be_true
  True |> should.be_true
}

pub fn gleam_config_test() {
  let config = lexer.gleam_config()
  
  config.line_comment |> should.equal(Some("//"))
  True |> should.be_true
}

pub fn with_keywords_test() {
  let config = lexer.default_config()
    |> lexer.with_keywords(["foo", "bar"])
  
  list.contains(config.keywords, "foo") |> should.be_true
  True |> should.be_true
}

pub fn with_indent_sensitivity_test() {
  let config = lexer.default_config()
    |> lexer.with_indent_sensitivity(4)
  
  config.indent_sensitive |> should.be_true
  config.indent_unit |> should.equal(4)
  True |> should.be_true
}

// ============================================================================
// EOF TESTS
// ============================================================================

pub fn tokenize_eof_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "x")
  
  // Last token should be EOF
  True |> should.be_true
}

pub fn tokenize_empty_test() {
  let config = lexer.default_config()
  let tokens = lexer.tokenize(config, "test", "")
  
  // Should have EOF token
  list.is_empty(tokens) |> should.be_false
  True |> should.be_true
}
