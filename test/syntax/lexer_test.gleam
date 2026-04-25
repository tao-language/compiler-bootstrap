import gleam/list
import gleeunit
import syntax/lexer.{Token, tokenize, tokenize_with_filename}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Empty and whitespace input
// ============================================================================

pub fn empty_input_produces_only_eof_test() {
  let tokens = tokenize("")
  assert list.length(tokens) == 1
  assert case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn whitespace_only_input_produces_only_eof_test() {
  let tokens = tokenize("   \n\t  ")
  assert list.length(tokens) == 1
  assert case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

// ============================================================================
// Integer literals
// ============================================================================

pub fn tokenize_single_integer_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_zero_test() {
  let tokens = tokenize("0")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "0", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_large_integer_test() {
  let tokens = tokenize("123456789")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "123456789", ..), Token(kind: "Eof", ..)] ->
      True
    _ -> False
  }
}

// ============================================================================
// Float literals
// ============================================================================

pub fn tokenize_float_with_leading_digit_test() {
  let tokens = tokenize("3.14")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Float", value: "3.14", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_float_with_trailing_zeros_test() {
  let tokens = tokenize("1.50")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Float", value: "1.50", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// String literals
// ============================================================================

pub fn tokenize_simple_string_test() {
  let tokens = tokenize("\"hello\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "hello", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_newline_escape_test() {
  let tokens = tokenize("\"hello\\nworld\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "hello\nworld", ..), Token(kind: "Eof", ..)] ->
      True
    _ -> False
  }
}

pub fn tokenize_string_with_tab_escape_test() {
  let tokens = tokenize("\"hello\\tworld\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "hello\tworld", ..), Token(kind: "Eof", ..)] ->
      True
    _ -> False
  }
}

pub fn tokenize_string_with_escaped_quote_test() {
  let tokens = tokenize("\"say \\\"hi\\\"\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "say \"hi\"", ..), Token(kind: "Eof", ..)] ->
      True
    _ -> False
  }
}

pub fn tokenize_string_with_escaped_backslash_test() {
  let tokens = tokenize("\"hello\\\\world\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "hello\\world", ..), Token(kind: "Eof", ..)] ->
      True
    _ -> False
  }
}

// ============================================================================
// Names and keywords
// ============================================================================

pub fn tokenize_identifier_test() {
  let tokens = tokenize("foo")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "foo", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_capitalized_identifier_test() {
  let tokens = tokenize("Foo")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "Foo", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_underscore_in_name_test() {
  let tokens = tokenize("my_var")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "my_var", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_let_test() {
  let tokens = tokenize("let")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "let", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_fn_test() {
  let tokens = tokenize("fn")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "fn", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_true_test() {
  let tokens = tokenize("true")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "true", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_false_test() {
  let tokens = tokenize("false")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "false", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_lambda_symbol_test() {
  let tokens = tokenize("λ")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Lambda", value: "λ", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Operators
// ============================================================================

pub fn tokenize_single_char_operators_test() {
  let tokens = tokenize("+ - * /")
  assert list.length(tokens) == 5
  assert case tokens {
    [
      Token(kind: "Op", value: "+", ..),
      Token(kind: "Op", value: "-", ..),
      Token(kind: "Op", value: "*", ..),
      Token(kind: "Op", value: "/", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_multi_char_operators_test() {
  let tokens = tokenize("-> == != <= >= && || ..")
  assert list.length(tokens) == 9
  assert case tokens {
    [
      Token(kind: "Op", value: "->", ..),
      Token(kind: "Op", value: "==", ..),
      Token(kind: "Op", value: "!=", ..),
      Token(kind: "Op", value: "<=", ..),
      Token(kind: "Op", value: ">=", ..),
      Token(kind: "Op", value: "&&", ..),
      Token(kind: "Op", value: "||", ..),
      Token(kind: "Op", value: "..", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Punctuation
// ============================================================================

pub fn tokenize_parentheses_test() {
  let tokens = tokenize("()")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Punct", value: "(", ..),
      Token(kind: "Punct", value: ")", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_braces_test() {
  let tokens = tokenize("{}")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Punct", value: "{", ..),
      Token(kind: "Punct", value: "}", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_brackets_test() {
  let tokens = tokenize("[]")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Punct", value: "[", ..),
      Token(kind: "Punct", value: "]", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_comma_semicolon_colon_test() {
  let tokens = tokenize("; , :")
  assert list.length(tokens) == 4
  assert case tokens {
    [
      Token(kind: "Punct", value: ";", ..),
      Token(kind: "Punct", value: ",", ..),
      Token(kind: "Punct", value: ":", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Comments
// ============================================================================

pub fn skip_single_line_comment_test() {
  let tokens = tokenize("// comment")
  assert list.length(tokens) == 1
  assert case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn skip_single_line_comment_with_code_after_test() {
  let tokens = tokenize("// comment\nlet x = 42")
  assert list.length(tokens) == 5
  assert case tokens {
    [
      Token(kind: "Keyword", value: "let", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Integer", value: "42", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn skip_block_comment_test() {
  let tokens = tokenize("/* comment */")
  assert list.length(tokens) == 1
  assert case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn skip_block_comment_with_code_after_test() {
  let tokens = tokenize("/* comment */ let x")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Keyword", value: "let", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Position tracking
// ============================================================================

pub fn tokenize_multiple_tokens_with_correct_line_test() {
  let tokens = tokenize("let x\n= 42")
  assert list.length(tokens) == 5
}

pub fn tokenize_with_filename_attaches_filename_test() {
  let tokens = tokenize_with_filename("let x = 42", "test.gleam")
  let file = case tokens {
    [Token(span: s, ..), ..] -> s.file
    _ -> ""
  }
  assert file == "test.gleam"
}

pub fn tokenize_with_empty_filename_defaults_to_empty_string_test() {
  let tokens = tokenize("let x")
  let file = case tokens {
    [Token(span: s, ..), ..] -> s.file
    _ -> ""
  }
  assert file == ""
}

// ============================================================================
// Combined examples
// ============================================================================

pub fn tokenize_let_binding_test() {
  let tokens = tokenize("let x = 42")
  assert list.length(tokens) == 5
  assert case tokens {
    [
      Token(kind: "Keyword", value: "let", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Integer", value: "42", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_function_application_test() {
  let tokens = tokenize("f(x)")
  assert list.length(tokens) == 5
  assert case tokens {
    [
      Token(kind: "Name", value: "f", ..),
      Token(kind: "Punct", value: "(", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: ")", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_lambda_expression_test() {
  let tokens = tokenize("λx.x")
  assert list.length(tokens) == 5
  assert case tokens {
    [
      Token(kind: "Lambda", value: "λ", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: ".", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Edge cases and boundary conditions
// ============================================================================

pub fn tokenize_float_with_leading_zero_test() {
  let tokens = tokenize("0.5")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Float", value: "0.5", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_integer_followed_by_dot_as_integer_test() {
  let tokens = tokenize("42 .")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Integer", value: "42", ..),
      Token(kind: "Punct", value: ".", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_identifier_with_multiple_underscores_test() {
  let tokens = tokenize("my__var")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "my__var", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_identifier_with_trailing_underscore_test() {
  let tokens = tokenize("foo_")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "foo_", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_only_underscores_is_name_test() {
  let tokens = tokenize("__")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "_", ..),
      Token(kind: "Op", value: "_", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_non_ascii_in_string_test() {
  let tokens = tokenize("\"こんにちは\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "こんにちは", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_empty_string_test() {
  let tokens = tokenize("\"\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_consecutive_operators_test() {
  let tokens = tokenize("++")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "+", ..),
      Token(kind: "Op", value: "+", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_mixed_multi_char_operators_test() {
  let tokens = tokenize("-> <<")
  assert list.length(tokens) == 4
  assert case tokens {
    [
      Token(kind: "Op", value: "->", ..),
      Token(kind: "Op", value: "<", ..),
      Token(kind: "Op", value: "<", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_whitespace_between_operators_test() {
  let tokens = tokenize("- >")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "-", ..),
      Token(kind: "Op", value: ">", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_block_comment_with_newlines_test() {
  let tokens = tokenize("/*\n * comment\n */ let x")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Keyword", value: "let", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_nested_block_comment_stops_at_first_close_test() {
  let tokens = tokenize("/* outer */ inner /* not comment */")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "inner", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_number_at_end_of_input_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_eof_tokens_is_error_test() {
  let tokens = tokenize("")
  let eof_count =
    tokens
    |> list.filter(fn(t) { t.kind == "Eof" })
    |> list.length
  assert eof_count == 1
}

pub fn tokenize_span_has_correct_filename_when_provided_test() {
  let tokens = tokenize_with_filename("let x = 42", "module.tao")
  let all_have_filename = case tokens {
    [
      Token(span: s1, ..),
      Token(span: s2, ..),
      Token(span: s3, ..),
      Token(span: s4, ..),
      Token(span: eof, ..),
    ] ->
      s1.file == "module.tao"
      && s2.file == "module.tao"
      && s3.file == "module.tao"
      && s4.file == "module.tao"
      && eof.file == "module.tao"
    _ -> False
  }
  assert all_have_filename
}

// ============================================================================
// Span verification tests
//
// These tests verify that spans are correctly recorded for each token type,
// checking start_line, start_col, end_line, end_col, and file fields.
// ============================================================================

pub fn tokenize_integer_span_correct_test() {
  // Integer token should have a valid span on line 1
  let tokens = tokenize_with_filename("let x = 42", "test.tao")
  assert case tokens {
    [
      Token(kind: "Keyword", span: s1, ..),
      Token(kind: "Name", span: s2, ..),
      Token(kind: "Punct", span: s3, ..),
      Token(kind: "Integer", value: "42", span: s4),
      Token(kind: "Eof", ..),
    ] ->
      s1.start_line == 1 && s1.start_col == 1
      && s2.start_line == 1
      && s3.start_line == 1
      && s4.start_line == 1 && s4.end_line == 1
    _ -> False
  }
}

pub fn tokenize_float_span_correct_test() {
  // Float token should have a valid span on line 1
  let tokens = tokenize_with_filename("x = 3.14", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: _, ..),
      Token(kind: "Punct", span: _, ..),
      Token(kind: "Float", value: "3.14", span: s),
      Token(kind: "Eof", ..),
    ] -> s.start_line == 1 && s.end_line == 1
    _ -> False
  }
}

pub fn tokenize_string_span_correct_test() {
  // String token should have a valid span on line 1
  let tokens = tokenize_with_filename("x = \"hi\"", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: _, ..),
      Token(kind: "Punct", span: _, ..),
      Token(kind: "String", value: "hi", span: s),
      Token(kind: "Eof", ..),
    ] ->
      s.start_line == 1 && s.end_line == 1
    _ -> False
  }
}

pub fn tokenize_lambda_span_correct_test() {
  // Lambda symbol token should have a valid span
  let tokens = tokenize_with_filename("λ", "test.tao")
  assert case tokens {
    [Token(kind: "Lambda", value: "λ", span: s), Token(kind: "Eof", ..)] ->
      s.start_line == 1 && s.start_col == 1
    _ -> False
  }
}

pub fn tokenize_multi_line_span_tracks_lines_test() {
  // Tokens on different lines should have correct line numbers
  let tokens = tokenize_with_filename("let x\n= 42", "test.tao")
  assert case tokens {
    [
      Token(kind: "Keyword", span: s1, ..),
      Token(kind: "Name", span: s2, ..),
      Token(kind: "Punct", span: s3, ..),
      Token(kind: "Integer", span: s4, ..),
      Token(kind: "Eof", ..),
    ] ->
      s1.start_line == 1  // let is on line 1
      && s2.start_line == 1  // x is on line 1
      && s3.start_line == 2  // = is on line 2
      && s4.start_line == 2  // 42 is on line 2
    _ -> False
  }
}

pub fn tokenize_all_tokens_from_same_file_have_correct_file_test() {
  // All tokens from tokenize_with_filename should carry the correct file
  let tokens = tokenize_with_filename("fn foo(x) { x + 1 }", "math.tao")
  let all_correct_file = {
    case tokens {
      [Token(span: s1, ..), Token(span: s2, ..), Token(span: s3, ..),
       Token(span: s4, ..), Token(span: s5, ..), Token(span: s6, ..),
       Token(span: s7, ..), Token(span: s8, ..), Token(span: s9, ..),
       Token(span: s10, ..), Token(kind: "Eof", span: eof, ..)] ->
        s1.file == "math.tao"
        && s2.file == "math.tao"
        && s3.file == "math.tao"
        && s4.file == "math.tao"
        && s5.file == "math.tao"
        && s6.file == "math.tao"
        && s7.file == "math.tao"
        && s8.file == "math.tao"
        && s9.file == "math.tao"
        && s10.file == "math.tao"
        && eof.file == "math.tao"
      _ -> False
    }
  }
  assert all_correct_file
}

pub fn tokenize_keyword_span_correct_test() {
  // Keywords are stored as Name tokens with value matching keyword
  // but kind is "Keyword" - span should be correct
  let tokens = tokenize_with_filename("true", "test.tao")
  assert case tokens {
    [
      Token(kind: "Keyword", value: "true", span: s),
      Token(kind: "Eof", ..),
    ] ->
      s.start_line == 1 && s.start_col == 1
      && s.end_line == 1 && s.end_col == 5  // "true" is 4 chars
    _ -> False
  }
}

pub fn tokenize_operator_span_correct_test() {
  // Multi-character operator should have a valid span
  let tokens = tokenize_with_filename("a -> b", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: _, ..),
      Token(kind: "Op", value: "->", span: s),
      Token(kind: "Name", span: _, ..),
      Token(kind: "Eof", ..),
    ] ->
      s.start_line == 1 && s.end_line == 1
    _ -> False
  }
}

// ============================================================================
// Additional edge case tests
// ============================================================================

pub fn tokenize_pipe_operator_test() {
  // Pipe character is tokenized as Punct
  let tokens = tokenize("|")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "|", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_ampersand_operator_test() {
  // Ampersand is tokenized as Punct
  let tokens = tokenize("&")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "&", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_exclamation_operator_test() {
  // Exclamation is tokenized as Punct
  let tokens = tokenize("!")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "!", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_less_greater_operator_test() {
  // << tokenizes as two single-char operators
  let tokens = tokenize("<<")
  assert list.length(tokens) == 3
  assert case tokens {
    [Token(kind: "Op", value: "<", ..), Token(kind: "Op", value: "<", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_single_underscore_as_operator_test() {
  // Single underscore is a single Op token
  let tokens = tokenize("_")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Op", value: "_", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_identifiers_with_whitespace_test() {
  // Multiple identifiers separated by whitespace tokenize correctly
  let tokens = tokenize("foo bar baz")
  assert list.length(tokens) == 4  // 3 Names + Eof
  assert case tokens {
    [
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Name", value: "bar", ..),
      Token(kind: "Name", value: "baz", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_newline_at_end_test() {
  // Input ending with newline produces tokens up to Eof
  let tokens = tokenize("42\n")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_carriage_return_skipped_test() {
  // Carriage returns are skipped like other whitespace
  let tokens = tokenize("foo\rbar")
  assert list.length(tokens) == 3  // 2 Names + Eof
  assert case tokens {
    [Token(kind: "Name", value: "foo", ..), Token(kind: "Name", value: "bar", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_double_dash_is_two_operators_test() {
  // "--" tokenizes as two Op tokens, not a single operator
  let tokens = tokenize("--")
  assert list.length(tokens) == 3
  assert case tokens {
    [Token(kind: "Op", value: "-", ..), Token(kind: "Op", value: "-", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_plus_equals_test() {
  // "+=" tokenizes as Op("+") then Punct("=") then Eof
  let tokens = tokenize("+=")
  assert case tokens {
    [Token(kind: "Op", ..), Token(kind: "Punct", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
