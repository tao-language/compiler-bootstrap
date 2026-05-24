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

pub fn tokenize_string_with_escaped_quote_test() {
  let tokens = tokenize("\"say \\\"hi\\\"\"")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "String", value: "say \"hi\"", ..), Token(kind: "Eof", ..)] ->
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

pub fn tokenize_underscore_in_name_test() {
  let tokens = tokenize("my_var")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "my_var", ..), Token(kind: "Eof", ..)] -> True
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

pub fn tokenize_integer_span_correct_test() {
  let tokens = tokenize_with_filename("x = 42", "test.tao")
  assert case tokens {
    [
      Token(kind: "Name", span: _, ..),
      Token(kind: "Punct", span: _, ..),
      Token(kind: "Integer", value: "42", span: s),
      Token(kind: "Eof", ..),
    ] -> s.start_line == 1 && s.end_line == 1
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
    ] -> s1.start_line == 1 && s2.start_line == 2 && s3.start_line == 2
    _ -> False
  }
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

pub fn tokenize_only_underscores_is_operators_test() {
  // Underscores are identifier characters, so "__" is a single identifier
  let tokens = tokenize("__")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "__", ..), Token(kind: "Eof", ..)] -> True
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

pub fn tokenize_carriage_return_skipped_test() {
  let tokens = tokenize("foo\rbar")
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

pub fn tokenize_double_dash_is_two_operators_test() {
  let tokens = tokenize("--")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "-", ..),
      Token(kind: "Op", value: "-", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_plus_equals_is_op_and_punct_test() {
  let tokens = tokenize("+=")
  assert case tokens {
    [Token(kind: "Op", ..), Token(kind: "Punct", ..), Token(kind: "Eof", ..)] ->
      True
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
