import gleam/list
import gleeunit
import syntax/base_lexer.{Token, tokenize, tokenize_with_filename}

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
// Names (identifiers — all identifiers are "Name" in the base lexer)
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

pub fn tokenize_underscore_in_name_leading_test() {
  let tokens = tokenize("_var")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "_var", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_mixed_case_identifier_test() {
  let tokens = tokenize("camelCase")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "camelCase", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_numbers_in_identifier_test() {
  let tokens = tokenize("foo123")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "foo123", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Single-character operators
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

pub fn tokenize_less_greater_test() {
  let tokens = tokenize("< >")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "<", ..),
      Token(kind: "Op", value: ">", ..),
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

pub fn tokenize_pipe_operator_test() {
  let tokens = tokenize("|")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "|", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_ampersand_operator_test() {
  let tokens = tokenize("&")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "&", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_exclamation_operator_test() {
  let tokens = tokenize("!")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "!", ..), Token(kind: "Eof", ..)] -> True
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
  let tokens = tokenize("// comment\nfoo bar")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Name", value: "bar", ..),
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
  let tokens = tokenize("/* comment */ foo bar")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Name", value: "bar", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_block_comment_with_newlines_test() {
  let tokens = tokenize("/*\n * comment\n */ foo bar")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Name", value: "bar", ..),
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

// ============================================================================
// Position tracking
// ============================================================================

pub fn tokenize_with_filename_attaches_filename_test() {
  let tokens = tokenize_with_filename("foo bar", "test.gleam")
  let file = case tokens {
    [Token(span: s, ..), ..] -> s.file
    _ -> ""
  }
  assert file == "test.gleam"
}

pub fn tokenize_with_empty_filename_defaults_to_empty_string_test() {
  let tokens = tokenize("foo bar")
  let file = case tokens {
    [Token(span: s, ..), ..] -> s.file
    _ -> ""
  }
  assert file == ""
}

pub fn tokenize_span_has_correct_filename_when_provided_test() {
  let tokens = tokenize_with_filename("foo bar", "module.tao")
  let all_have_filename = case tokens {
    [
      Token(span: s1, ..),
      Token(span: s2, ..),
      Token(span: eof, ..),
    ] ->
      s1.file == "module.tao"
      && s2.file == "module.tao"
      && eof.file == "module.tao"
    _ -> False
  }
  assert all_have_filename
}

pub fn tokenize_integer_span_correct_test() {
  let tokens = tokenize_with_filename("x = 42", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: _, ..),
      Token(kind: "Punct", span: _, ..),
      Token(kind: "Integer", value: "42", span: s),
      Token(kind: "Eof", ..),
    ] ->
      s.start_line == 1 && s.end_line == 1
    _ -> False
  }
}

pub fn tokenize_float_span_correct_test() {
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

pub fn tokenize_multi_line_span_tracks_lines_test() {
  let tokens = tokenize_with_filename("foo\n= bar", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: s1, ..),
      Token(kind: "Punct", span: s2, ..),
      Token(kind: "Name", span: s3, ..),
      Token(kind: "Eof", ..),
    ] ->
      s1.start_line == 1
      && s2.start_line == 2
      && s3.start_line == 2
    _ -> False
  }
}

pub fn tokenize_all_tokens_from_same_file_have_correct_file_test() {
  let tokens = tokenize_with_filename("fn foo(x) { x + 1 }", "math.tao")
  let all_correct_file = case tokens {
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
  assert all_correct_file
}

// ============================================================================
// Combined examples
// ============================================================================

pub fn tokenize_identifier_assignment_test() {
  let tokens = tokenize("x = 42")
  assert list.length(tokens) == 4
  assert case tokens {
    [
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

pub fn tokenize_multiple_identifiers_test() {
  let tokens = tokenize("foo bar baz")
  assert list.length(tokens) == 4
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

// ============================================================================
// Edge cases
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

pub fn tokenize_only_underscores_is_operators_test() {
  // Underscores are identifier characters, so "__" is a single identifier
  let tokens = tokenize("__")
  assert list.length(tokens) == 2
  assert case tokens {
    [
      Token(kind: "Name", value: "__", ..),
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

pub fn tokenize_multiple_eof_tokens_is_error_test() {
  let tokens = tokenize("")
  let eof_count =
    tokens
    |> list.filter(fn(t) { t.kind == "Eof" })
    |> list.length
  assert eof_count == 1
}

pub fn tokenize_carriage_return_skipped_test() {
  let tokens = tokenize("foo\rbar")
  assert list.length(tokens) == 3
  assert case tokens {
    [Token(kind: "Name", value: "foo", ..), Token(kind: "Name", value: "bar", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_double_dash_is_two_operators_test() {
  let tokens = tokenize("--")
  assert list.length(tokens) == 3
  assert case tokens {
    [Token(kind: "Op", value: "-", ..), Token(kind: "Op", value: "-", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_plus_equals_is_op_and_punct_test() {
  let tokens = tokenize("+=")
  assert case tokens {
    [Token(kind: "Op", ..), Token(kind: "Punct", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_bare_dot_before_number_is_punct_plus_integer_test() {
  let tokens = tokenize(".5")
  assert case tokens {
    [
      Token(kind: "Punct", value: ".", ..),
      Token(kind: "Integer", value: "5", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_float_zero_point_zero_test() {
  let tokens = tokenize("0.0")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Float", value: "0.0", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_single_underscore_as_identifier_test() {
  let tokens = tokenize("_")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "_", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_newline_at_end_test() {
  let tokens = tokenize("42\n")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_statements_test() {
  let tokens = tokenize("x = 1\ny = 2")
  assert case tokens {
    [
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Integer", value: "1", ..),
      Token(kind: "Name", value: "y", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Integer", value: "2", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_pipe_is_punct_not_op_test() {
  // Pipe should be Punct in base lexer
  let tokens = tokenize("|")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Punct", value: "|", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
