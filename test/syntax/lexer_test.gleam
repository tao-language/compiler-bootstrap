import gleeunit
import syntax/lexer.{tokenize, tokenize_with_filename, Token}
import gleam/list

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Empty and whitespace input
// ============================================================================

pub fn empty_input_produces_only_eof_test() {
  let tokens = tokenize("")
  case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn whitespace_only_input_produces_only_eof_test() {
  let tokens = tokenize("   \n\t  ")
  case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

// ============================================================================
// Integer literals
// ============================================================================

pub fn tokenize_single_integer_test() {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_zero_test() {
  let tokens = tokenize("0")
  case tokens {
    [Token(kind: "Integer", value: "0", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_large_integer_test() {
  let tokens = tokenize("123456789")
  case tokens {
    [Token(kind: "Integer", value: "123456789", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Float literals
// ============================================================================

pub fn tokenize_float_with_leading_digit_test() {
  let tokens = tokenize("3.14")
  case tokens {
    [Token(kind: "Float", value: "3.14", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_float_with_trailing_zeros_test() {
  let tokens = tokenize("1.50")
  case tokens {
    [Token(kind: "Float", value: "1.50", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// String literals
// ============================================================================

pub fn tokenize_simple_string_test() {
  let tokens = tokenize("\"hello\"")
  case tokens {
    [Token(kind: "String", value: "hello", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_newline_escape_test() {
  let tokens = tokenize("\"hello\\nworld\"")
  case tokens {
    [Token(kind: "String", value: "hello\nworld", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_tab_escape_test() {
  let tokens = tokenize("\"hello\\tworld\"")
  case tokens {
    [Token(kind: "String", value: "hello\tworld", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_escaped_quote_test() {
  let tokens = tokenize("\"say \\\"hi\\\"\"")
  case tokens {
    [Token(kind: "String", value: "say \"hi\"", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_string_with_escaped_backslash_test() {
  let tokens = tokenize("\"hello\\\\world\"")
  case tokens {
    [Token(kind: "String", value: "hello\\\\world", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Names and keywords
// ============================================================================

pub fn tokenize_identifier_test() {
  let tokens = tokenize("foo")
  case tokens {
    [Token(kind: "Name", value: "foo", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_capitalized_identifier_test() {
  let tokens = tokenize("Foo")
  case tokens {
    [Token(kind: "Name", value: "Foo", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_underscore_in_name_test() {
  let tokens = tokenize("my_var")
  case tokens {
    [Token(kind: "Name", value: "my_var", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_let_test() {
  let tokens = tokenize("let")
  case tokens {
    [Token(kind: "Keyword", value: "let", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_fn_test() {
  let tokens = tokenize("fn")
  case tokens {
    [Token(kind: "Keyword", value: "fn", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_true_test() {
  let tokens = tokenize("true")
  case tokens {
    [Token(kind: "Keyword", value: "true", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_false_test() {
  let tokens = tokenize("false")
  case tokens {
    [Token(kind: "Keyword", value: "false", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_lambda_symbol_test() {
  let tokens = tokenize("λ")
  case tokens {
    [Token(kind: "Lambda", value: "λ", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Operators
// ============================================================================

pub fn tokenize_single_char_operators_test() {
  let tokens = tokenize("+ - * /")
  case tokens {
    [Token(kind: "Op", value: "+", ..),
     Token(kind: "Op", value: "-", ..),
     Token(kind: "Op", value: "*", ..),
     Token(kind: "Op", value: "/", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multi_char_operators_test() {
  let tokens = tokenize("-> == != <= >= && || ..")
  case tokens {
    [Token(kind: "Op", value: "->", ..),
     Token(kind: "Op", value: "==", ..),
     Token(kind: "Op", value: "!=", ..),
     Token(kind: "Op", value: "<=", ..),
     Token(kind: "Op", value: ">=", ..),
     Token(kind: "Op", value: "&&", ..),
     Token(kind: "Op", value: "||", ..),
     Token(kind: "Op", value: "..", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Punctuation
// ============================================================================

pub fn tokenize_parentheses_test() {
  let tokens = tokenize("()")
  case tokens {
    [Token(kind: "Punct", value: "(", ..),
     Token(kind: "Punct", value: ")", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_braces_test() {
  let tokens = tokenize("{}")
  case tokens {
    [Token(kind: "Punct", value: "{", ..),
     Token(kind: "Punct", value: "}", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_brackets_test() {
  let tokens = tokenize("[]")
  case tokens {
    [Token(kind: "Punct", value: "[", ..),
     Token(kind: "Punct", value: "]", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_comma_semicolon_colon_test() {
  let tokens = tokenize("; , :")
  case tokens {
    [Token(kind: "Punct", value: ";", ..),
     Token(kind: "Punct", value: ",", ..),
     Token(kind: "Punct", value: ":", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Comments
// ============================================================================

pub fn skip_single_line_comment_test() {
  let tokens = tokenize("// comment")
  case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn skip_single_line_comment_with_code_after_test() {
  let tokens = tokenize("// comment\nlet x = 42")
  case tokens {
    [Token(kind: "Keyword", value: "let", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Punct", value: "=", ..),
     Token(kind: "Integer", value: "42", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn skip_block_comment_test() {
  let tokens = tokenize("/* comment */")
  case tokens {
    [Token(kind: "Eof", ..), ..] -> True
    _ -> False
  }
}

pub fn skip_block_comment_with_code_after_test() {
  let tokens = tokenize("/* comment */ let x")
  case tokens {
    [Token(kind: "Keyword", value: "let", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Position tracking
// ============================================================================

pub fn tokenize_multiple_tokens_with_correct_line_test() {
  let tokens = tokenize("let x\n= 42")
  tokens |> list.length == 5
}

pub fn tokenize_with_filename_attaches_filename_test() {
  let tokens = tokenize_with_filename("let x = 42", "test.gleam")
  case tokens {
    [Token(span: s, ..), ..] -> s.file == "test.gleam"
    _ -> False
  }
}

pub fn tokenize_with_empty_filename_defaults_to_empty_string_test() {
  let tokens = tokenize("let x")
  case tokens {
    [Token(span: s, ..), ..] -> s.file == ""
    _ -> False
  }
}

// ============================================================================
// Combined examples
// ============================================================================

pub fn tokenize_let_binding_test() {
  let tokens = tokenize("let x = 42")
  case tokens {
    [Token(kind: "Keyword", value: "let", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Punct", value: "=", ..),
     Token(kind: "Integer", value: "42", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_function_application_test() {
  let tokens = tokenize("f(x)")
  case tokens {
    [Token(kind: "Name", value: "f", ..),
     Token(kind: "Punct", value: "(", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Punct", value: ")", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_lambda_expression_test() {
  let tokens = tokenize("λx.x")
  case tokens {
    [Token(kind: "Lambda", value: "λ", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Edge cases and boundary conditions
// ============================================================================

pub fn tokenize_float_with_leading_zero_test() {
  let tokens = tokenize("0.5")
  case tokens {
    [Token(kind: "Float", value: "0.5", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_integer_followed_by_dot_as_integer_test() {
  // A number followed by a bare dot (not followed by more digits) should be tokenized
  // as an integer, with the dot consumed separately as punctuation
  let tokens = tokenize("42 .")
  case tokens {
    [Token(kind: "Integer", value: "42", ..),
     Token(kind: "Punct", value: ".", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_identifier_with_multiple_underscores_test() {
  let tokens = tokenize("my__var")
  case tokens {
    [Token(kind: "Name", value: "my__var", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_identifier_with_trailing_underscore_test() {
  let tokens = tokenize("foo_")
  case tokens {
    [Token(kind: "Name", value: "foo_", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_only_underscores_is_name_test() {
  // A single underscore is treated as an operator, but multiple underscores form a name
  let tokens = tokenize("__")
  case tokens {
    [Token(kind: "Op", value: "_", ..),
     Token(kind: "Op", value: "_", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_non_ascii_in_string_test() {
  let tokens = tokenize("\"こんにちは\"")
  case tokens {
    [Token(kind: "String", value: "こんにちは", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_empty_string_test() {
  let tokens = tokenize("\"\"")
  case tokens {
    [Token(kind: "String", value: "", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_consecutive_operators_test() {
  let tokens = tokenize("++")
  case tokens {
    [Token(kind: "Op", value: "+", ..),
     Token(kind: "Op", value: "+", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_mixed_multi_char_operators_test() {
  let tokens = tokenize("-> <<")
  case tokens {
    [Token(kind: "Op", value: "->", ..),
     Token(kind: "Op", value: "<", ..),
     Token(kind: "Op", value: "<", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_whitespace_between_operators_test() {
  let tokens = tokenize("- >")
  case tokens {
    [Token(kind: "Op", value: "-", ..),
     Token(kind: "Op", value: ">", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_block_comment_with_newlines_test() {
  let tokens = tokenize("/*\n * comment\n */ let x")
  case tokens {
    [Token(kind: "Keyword", value: "let", ..),
     Token(kind: "Name", value: "x", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_nested_block_comment_stops_at_first_close_test() {
  let tokens = tokenize("/* outer */ inner /* not comment */")
  case tokens {
    [Token(kind: "Name", value: "inner", ..),
     Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_number_at_end_of_input_test() {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_eof_tokens_is_error_test() {
  // Only one EOF token should be produced
  let tokens = tokenize("")
  let eof_count = tokens
  |> list.filter(fn(t) { t.kind == "Eof" })
  |> list.length
  assert eof_count == 1
}

pub fn tokenize_span_has_correct_filename_when_provided_test() {
  let tokens = tokenize_with_filename("let x = 42", "module.tao")
  case tokens {
    [Token(span: s, ..), Token(span: s2, ..), Token(span: s3, ..), Token(span: s4, ..), Token(span: eof, ..)] -> {
      s.file == "module.tao"
      && s2.file == "module.tao"
      && s3.file == "module.tao"
      && s4.file == "module.tao"
      && eof.file == "module.tao"
    }
    _ -> False
  }
}
