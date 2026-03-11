// ============================================================================
// LEXER TESTS
// ============================================================================
/// Tests for the syntax/lexer module.
/// 
/// The lexer tokenizes source code into tokens with position information.
/// Each token has: kind, value, start, end, line, column
import gleam/list
import gleeunit
import gleeunit/should
import syntax/lexer.{type Token}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Get token kinds from a source string
fn tokenize_kinds(source: String) -> List(String) {
  lexer.tokenize(source) |> list.map(fn(t) { t.kind })
}

/// Get token values from a source string
fn tokenize_values(source: String) -> List(String) {
  lexer.tokenize(source) |> list.map(fn(t) { t.value })
}

/// Get a specific token by index
fn get_token(source: String, index: Int) -> Token {
  case list.drop(lexer.tokenize(source), index) {
    [token, ..] -> token
    [] -> lexer.Token("Error", "", 0, 0, 0, 0)
  }
}

// ============================================================================
// IDENTIFIER TESTS
// ============================================================================

pub fn tokenize_ident_simple_test() {
  tokenize_kinds("x") |> should.equal(["Ident"])
}

pub fn tokenize_ident_lowercase_test() {
  tokenize_values("foo") |> should.equal(["foo"])
}

pub fn tokenize_ident_uppercase_test() {
  tokenize_values("Foo") |> should.equal(["Foo"])
}

pub fn tokenize_ident_with_underscore_test() {
  tokenize_values("my_var") |> should.equal(["my_var"])
}

pub fn tokenize_ident_with_numbers_test() {
  tokenize_values("var1") |> should.equal(["var1"])
}

pub fn tokenize_ident_multiple_test() {
  tokenize_values("foo bar baz")
  |> should.equal(["foo", "bar", "baz"])
}

// ============================================================================
// KEYWORD TESTS
// ============================================================================

pub fn tokenize_keyword_let_test() {
  tokenize_kinds("let") |> should.equal(["Let"])
}

pub fn tokenize_keyword_fn_test() {
  tokenize_kinds("fn") |> should.equal(["Keyword"])
}

pub fn tokenize_keyword_match_test() {
  tokenize_kinds("match") |> should.equal(["Keyword"])
}

pub fn tokenize_keyword_mixed_with_idents_test() {
  tokenize_values("let x = fn")
  |> should.equal(["let", "x", "=", "fn"])
}

// ============================================================================
// NUMBER TESTS
// ============================================================================

pub fn tokenize_number_single_digit_test() {
  tokenize_values("0") |> should.equal(["0"])
}

pub fn tokenize_number_multi_digit_test() {
  tokenize_values("123") |> should.equal(["123"])
}

pub fn tokenize_number_multiple_test() {
  tokenize_values("1 2 3")
  |> should.equal(["1", "2", "3"])
}

pub fn tokenize_number_with_ident_test() {
  tokenize_values("x42")
  |> should.equal(["x42"])  // Should be identifier, not number
}

// ============================================================================
// STRING TESTS
// ============================================================================

pub fn tokenize_string_empty_test() {
  // String tokenizer returns the content (without quotes)
  let tokens = lexer.tokenize("\"\"")
  tokens |> list.length |> should.equal(1)
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal([""])
}

pub fn tokenize_string_simple_test() {
  let tokens = lexer.tokenize("\"hello\"")
  tokens |> list.length |> should.equal(1)
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["hello"])
}

pub fn tokenize_string_with_escape_n_test() {
  let tokens = lexer.tokenize("\"hello\\nworld\"")
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["hello\nworld"])
}

pub fn tokenize_string_with_escape_t_test() {
  let tokens = lexer.tokenize("\"hello\\tworld\"")
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["hello\tworld"])
}

pub fn tokenize_string_with_escape_quote_test() {
  let tokens = lexer.tokenize("\"hello\\\"world\"")
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["hello\"world"])
}

pub fn tokenize_string_with_escape_backslash_test() {
  let tokens = lexer.tokenize("\"hello\\\\world\"")
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["hello\\world"])
}

pub fn tokenize_string_multiple_test() {
  let tokens = lexer.tokenize("\"foo\" \"bar\"")
  tokens |> list.length |> should.equal(2)
  tokens |> list.map(fn(t) { t.kind }) |> should.equal(["String", "String"])
  tokens |> list.map(fn(t) { t.value }) |> should.equal(["foo", "bar"])
}

// ============================================================================
// OPERATOR TESTS
// ============================================================================

pub fn tokenize_operator_plus_test() {
  tokenize_kinds("+") |> should.equal(["Operator"])
}

pub fn tokenize_operator_minus_test() {
  tokenize_kinds("-") |> should.equal(["Operator"])
}

pub fn tokenize_operator_star_test() {
  tokenize_kinds("*") |> should.equal(["Operator"])
}

pub fn tokenize_operator_slash_test() {
  tokenize_kinds("/") |> should.equal(["Operator"])
}

pub fn tokenize_operator_equals_test() {
  tokenize_kinds("=") |> should.equal(["Equal"])
}

pub fn tokenize_operator_arrow_test() {
  tokenize_kinds("->") |> should.equal(["Arrow"])
}

pub fn tokenize_operator_lambda_test() {
  tokenize_kinds("λ") |> should.equal(["Lambda"])
}

pub fn tokenize_operator_dot_test() {
  tokenize_kinds(".") |> should.equal(["Dot"])
}

pub fn tokenize_operator_colon_test() {
  tokenize_kinds(":") |> should.equal(["Colon"])
}

pub fn tokenize_operator_comma_test() {
  tokenize_kinds(",") |> should.equal(["Comma"])
}

pub fn tokenize_operator_multiple_test() {
  tokenize_values("+ - * /")
  |> should.equal(["+", "-", "*", "/"])
}

// ============================================================================
// PUNCTUATION TESTS
// ============================================================================

pub fn tokenize_paren_lparen_test() {
  tokenize_kinds("(") |> should.equal(["LParen"])
}

pub fn tokenize_paren_rparen_test() {
  tokenize_kinds(")") |> should.equal(["RParen"])
}

pub fn tokenize_brace_lbrace_test() {
  tokenize_kinds("{") |> should.equal(["LBrace"])
}

pub fn tokenize_brace_rbrace_test() {
  tokenize_kinds("}") |> should.equal(["RBrace"])
}

// ============================================================================
// WHITESPACE TESTS
// ============================================================================

pub fn tokenize_whitespace_space_test() {
  // Spaces should be skipped
  tokenize_values("x y") |> should.equal(["x", "y"])
}

pub fn tokenize_whitespace_tab_test() {
  // Tabs should be skipped
  tokenize_values("x\ty") |> should.equal(["x", "y"])
}

pub fn tokenize_whitespace_newline_test() {
  // Newlines should be skipped
  tokenize_values("x\ny") |> should.equal(["x", "y"])
}

pub fn tokenize_whitespace_multiple_test() {
  // Multiple whitespace chars should be skipped
  tokenize_values("x  \t\n  y") |> should.equal(["x", "y"])
}

// ============================================================================
// COMMENT TESTS
// ============================================================================

pub fn tokenize_comment_line_test() {
  // Line comments should be skipped
  tokenize_values("x // comment\ny")
  |> should.equal(["x", "y"])
}

pub fn tokenize_comment_line_at_end_test() {
  // Line comment at end of file
  tokenize_values("x // comment")
  |> should.equal(["x"])
}

pub fn tokenize_comment_block_test() {
  // Block comments should be skipped
  tokenize_values("x /* comment */ y")
  |> should.equal(["x", "y"])
}

pub fn tokenize_comment_block_multiline_test() {
  // Multi-line block comments
  tokenize_values("x /* line1\nline2 */ y")
  |> should.equal(["x", "y"])
}

pub fn tokenize_comment_nested_test() {
  // Nested block comments (inner */ ends outer)
  tokenize_values("x /* outer /* inner */ y")
  |> should.equal(["x", "y"])
}

// ============================================================================
// POSITION TESTS
// ============================================================================

pub fn tokenize_position_first_token_test() {
  // First token should be at line 1, column 1
  let token = get_token("x", 0)
  token.line |> should.equal(1)
  token.column |> should.equal(1)
}

pub fn tokenize_position_start_offset_test() {
  // First token should start at offset 0
  let token = get_token("x", 0)
  token.start |> should.equal(0)
  token.end |> should.equal(1)
}

pub fn tokenize_position_second_token_test() {
  // Second token after space
  let token = get_token("x y", 1)
  token.line |> should.equal(1)
  token.column |> should.equal(3)
}

pub fn tokenize_position_after_newline_test() {
  // Token after newline should be on line 2
  let token = get_token("x\ny", 1)
  token.line |> should.equal(2)
  token.column |> should.equal(1)
}

pub fn tokenize_position_multi_line_test() {
  // Multiple lines
  let token = get_token("x\ny\nz", 2)
  token.line |> should.equal(3)
  token.column |> should.equal(1)
}

pub fn tokenize_position_after_comment_test() {
  // Position after line comment
  let token = get_token("x // comment\ny", 1)
  token.line |> should.equal(2)
  token.column |> should.equal(1)
}

pub fn tokenize_position_lambda_test() {
  // Unicode lambda character
  let token = get_token("λx. x", 0)
  token.kind |> should.equal("Lambda")
  token.value |> should.equal("λ")
  token.start |> should.equal(0)
  token.end |> should.equal(1)
}

pub fn tokenize_position_column_after_lambda_test() {
  // Column after unicode lambda
  let token = get_token("λx. x", 1)
  token.column |> should.equal(2)  // After λ (1 char)
}

// ============================================================================
// COMPLEX INPUT TESTS
// ============================================================================

pub fn tokenize_lambda_expression_test() {
  let source = "λx. x + 1"
  let tokens = lexer.tokenize(source)

  tokens |> list.length |> should.equal(6)
  tokenize_values(source)
  |> should.equal(["λ", "x", ".", "x", "+", "1"])
}

pub fn tokenize_function_definition_test() {
  let source = "fn add(x, y) { x + y }"
  let tokens = lexer.tokenize(source)

  tokens |> list.length |> should.equal(12)
}

pub fn tokenize_match_expression_test() {
  let source = "match x { A → 1, B → 2 }"
  let tokens = lexer.tokenize(source)

  tokens |> list.length |> should.equal(11)
}

pub fn tokenize_record_test() {
  let source = "{x: 1, y: 2}"
  let tokens = lexer.tokenize(source)
  
  tokens |> list.length |> should.equal(9)
}

pub fn tokenize_nested_parens_test() {
  let source = "((x))"
  let tokens = lexer.tokenize(source)
  
  tokens |> list.length |> should.equal(5)
  tokenize_values(source)
  |> should.equal(["(", "(", "x", ")", ")"])
}

// ============================================================================
// ERROR CASES
// ============================================================================

pub fn tokenize_empty_input_test() {
  lexer.tokenize("") |> list.length |> should.equal(0)
}

pub fn tokenize_whitespace_only_test() {
  lexer.tokenize("   \n\t  ") |> list.length |> should.equal(0)
}

pub fn tokenize_comment_only_test() {
  lexer.tokenize("// comment") |> list.length |> should.equal(0)
}

pub fn tokenize_block_comment_only_test() {
  lexer.tokenize("/* comment */") |> list.length |> should.equal(0)
}

pub fn tokenize_dollar_i32_test() {
  tokenize_kinds("$I32") |> should.equal(["Dollar", "Ident"])
  tokenize_values("$I32") |> should.equal(["$", "I32"])
}

pub fn tokenize_hash_true_test() {
  tokenize_kinds("#True") |> should.equal(["Hash", "Ident"])
  tokenize_values("#True") |> should.equal(["#", "True"])
}
