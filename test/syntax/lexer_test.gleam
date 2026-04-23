// ============================================================================
// LEXER TESTS
// ============================================================================
/// Tests for the syntax/lexer module.
import gleam/list
import gleeunit
import syntax/lexer

pub fn main() {
  gleeunit.main()
}

/// Get token kinds from a source string
fn token_kinds_of(source: String) -> List(String) {
  let tokens = lexer.tokenize(source, "test")
  list.map(tokens, fn(t) { t.kind })
}

// ============================================================================
// TEST CASES
// ============================================================================

pub fn tokenize_identifiers_test() {
  assert token_kinds_of("foo") == ["Ident"]
  assert token_kinds_of("bar") == ["Ident"]
  assert token_kinds_of("_private") == ["Ident"]
  assert token_kinds_of("CamelCase") == ["Ident"]
}

pub fn tokenize_keywords_test() {
  assert token_kinds_of("let") == ["Keyword"]
  assert token_kinds_of("fn") == ["Keyword"]
  assert token_kinds_of("case") == ["Keyword"]
  assert token_kinds_of("in") == ["In"]
  assert token_kinds_of("if") == ["Keyword"]
  assert token_kinds_of("else") == ["Keyword"]
  assert token_kinds_of("type") == ["Keyword"]
  assert token_kinds_of("true") == ["Keyword"]
  assert token_kinds_of("false") == ["Keyword"]
}

pub fn tokenize_strings_test() {
  assert token_kinds_of("\"hello\"") == ["String"]
  assert token_kinds_of("\"world\"") == ["String"]
}

pub fn tokenize_numbers_test() {
  assert token_kinds_of("123") == ["Number"]
  assert token_kinds_of("42") == ["Number"]
}

pub fn tokenize_operators_test() {
  assert token_kinds_of("+") == ["Operator"]
  assert token_kinds_of("-") == ["Operator"]
  assert token_kinds_of("*") == ["Operator"]
  assert token_kinds_of("/") == ["Operator"]
  assert token_kinds_of("!") == ["Operator"]
  assert token_kinds_of(">") == ["Operator"]
  assert token_kinds_of("<") == ["Operator"]
  
  assert token_kinds_of("=") == ["Equal"]
  assert token_kinds_of("==") == ["Equal"]
  assert token_kinds_of("!=") == ["NotEqual"]
  assert token_kinds_of("->") == ["Arrow"]
  assert token_kinds_of("<-") == ["Arrow"]
  assert token_kinds_of("..") == ["DotDot"]
  assert token_kinds_of("=>") == ["FatArrow"]
  
  // Single & is an Operator
  assert token_kinds_of("&") == ["Operator"]
  // && is AmpersandAmpersand
  assert token_kinds_of("&&") == ["AmpersandAmpersand"]
}

pub fn tokenize_punctuation_test() {
  assert token_kinds_of("(") == ["LParen"]
  assert token_kinds_of(")") == ["RParen"]
  assert token_kinds_of("{") == ["LBrace"]
  assert token_kinds_of("}") == ["RBrace"]
  assert token_kinds_of("[") == ["LBracket"]
  assert token_kinds_of("]") == ["RBracket"]
  assert token_kinds_of(",") == ["Comma"]
  assert token_kinds_of(";") == ["Semi"]
  assert token_kinds_of(".") == ["Dot"]
  assert token_kinds_of(":") == ["Colon"]
}

pub fn tokenize_whitespace_test() {
  assert token_kinds_of("foo bar") == ["Ident", "Ident"]
  assert token_kinds_of("let x") == ["Keyword", "Ident"]
}

pub fn tokenize_multiple_tokens_test() {
  assert token_kinds_of("let x = 1") == ["Keyword", "Ident", "Equal", "Number"]
}

pub fn tokenize_case_expression_test() {
  assert token_kinds_of("case x of {") == ["Keyword", "Ident", "Ident", "LBrace"]
}

pub fn tokenize_function_call_test() {
  assert token_kinds_of("foo(bar)") == ["Ident", "LParen", "Ident", "RParen"]
}

pub fn tokenize_string_with_escaped_chars_test() {
  assert token_kinds_of("\"hello\\nworld\"") == ["String"]
}

pub fn tokenize_lambda_test() {
  assert token_kinds_of("λ") == ["Lambda"]
}

pub fn tokenize_question_mark_test() {
  assert token_kinds_of("?") == ["Question"]
}

pub fn tokenize_backslash_test() {
  assert token_kinds_of("\\") == ["Backslash"]
}

pub fn tokenize_assign_operator_test() {
  assert token_kinds_of(":=") == ["Assign"]
}
