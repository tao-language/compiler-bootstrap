/// Tests for the Tao lexer (language-specific)
///
/// Tests cover Tao-specific constructs that are NOT in the base lexer:
/// - Keywords (let, fn, true, false, if, else, case, etc.)
/// - Multi-character operators (->, ==, !=, <=, >=, &&, ||, ..)
/// - Lambda symbol (λ)

import gleeunit
import tao/lexer.{tokenize}
import syntax/base_lexer.{Token}
import gleam/list

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Keywords
// ============================================================================

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

pub fn tokenize_keyword_if_test() {
  let tokens = tokenize("if")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "if", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_case_test() {
  let tokens = tokenize("case")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "case", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_while_test() {
  let tokens = tokenize("while")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "while", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_for_test() {
  let tokens = tokenize("for")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Keyword", value: "for", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_and_or_not_test() {
  let and_tokens = tokenize("and")
  let or_tokens = tokenize("or")
  let not_tokens = tokenize("not")
  assert case and_tokens {
    [Token(kind: "Keyword", value: "and", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case or_tokens {
    [Token(kind: "Keyword", value: "or", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case not_tokens {
    [Token(kind: "Keyword", value: "not", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_keyword_pub_import_test() {
  let pub_tokens = tokenize("pub")
  let import_tokens = tokenize("import")
  assert case pub_tokens {
    [Token(kind: "Keyword", value: "pub", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case import_tokens {
    [Token(kind: "Keyword", value: "import", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn identifier_that_looks_like_keyword_but_is_not_test() {
  // "letting" is NOT a keyword (only "let" is)
  let tokens = tokenize("letting")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Name", value: "letting", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

// ============================================================================
// Multi-character operators
// ============================================================================

pub fn tokenize_arrow_operator_test() {
  let tokens = tokenize("->")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Op", value: "->", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_comparison_operators_test() {
  let eq_tokens = tokenize("==")
  let neq_tokens = tokenize("!=")
  assert case eq_tokens {
    [Token(kind: "Op", value: "==", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case neq_tokens {
    [Token(kind: "Op", value: "!=", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_less_greater_comparison_test() {
  let le_tokens = tokenize("<=")
  let ge_tokens = tokenize(">=")
  assert case le_tokens {
    [Token(kind: "Op", value: "<=", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case ge_tokens {
    [Token(kind: "Op", value: ">=", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_logical_operators_test() {
  let and_tokens = tokenize("&&")
  let or_tokens = tokenize("||")
  assert case and_tokens {
    [Token(kind: "Op", value: "&&", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case or_tokens {
    [Token(kind: "Op", value: "||", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_range_operator_test() {
  let tokens = tokenize("..")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Op", value: "..", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_forward_and_back_arrow_test() {
  let fwd = tokenize("->")
  let bwd = tokenize("<-")
  assert case fwd {
    [Token(kind: "Op", value: "->", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case bwd {
    [Token(kind: "Op", value: "<-", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_multiple_multi_char_operators_test() {
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
// Lambda symbol
// ============================================================================

pub fn tokenize_lambda_symbol_test() {
  let tokens = tokenize("λ")
  assert list.length(tokens) == 2
  assert case tokens {
    [Token(kind: "Lambda", value: "λ", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_lambda_with_params_test() {
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

pub fn tokenize_lambda_arrow_not_confused_test() {
  // λ followed by > should be Lambda + Op(">"
  let tokens = tokenize("λ>")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Lambda", value: "λ", ..),
      Token(kind: "Op", value: ">", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Combined Tao examples
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

pub fn tokenize_fn_definition_test() {
  let tokens = tokenize("fn foo(x) = x")
  assert list.length(tokens) == 8
  assert case tokens {
    [
      Token(kind: "Keyword", value: "fn", ..),
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Punct", value: "(", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: ")", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_function_with_arrow_test() {
  let tokens = tokenize("fn foo(x): Int -> Int = x")
  assert list.length(tokens) == 12
  assert case tokens {
    [
      Token(kind: "Keyword", value: "fn", ..),
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Punct", value: "(", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: ")", ..),
      Token(kind: "Punct", value: ":", ..),
      Token(kind: "Name", value: "Int", ..),
      Token(kind: "Op", value: "->", ..),
      Token(kind: "Name", value: "Int", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_if_expression_test() {
  let tokens = tokenize("if true then foo else bar")
  assert list.length(tokens) == 7
  assert case tokens {
    [
      Token(kind: "Keyword", value: "if", ..),
      Token(kind: "Keyword", value: "true", ..),
      Token(kind: "Keyword", value: "then", ..),
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Keyword", value: "else", ..),
      Token(kind: "Name", value: "bar", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_comparison_in_expression_test() {
  let tokens = tokenize("x == y && z != w")
  assert list.length(tokens) == 8
  assert case tokens {
    [
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Op", value: "==", ..),
      Token(kind: "Name", value: "y", ..),
      Token(kind: "Op", value: "&&", ..),
      Token(kind: "Name", value: "z", ..),
      Token(kind: "Op", value: "!=", ..),
      Token(kind: "Name", value: "w", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_fn_type_with_integer_test() {
  let tokens = tokenize("fn add(x: Int, y: Int) -> Int = x + y")
  assert list.length(tokens) == 18
  assert case tokens {
    [
      Token(kind: "Keyword", value: "fn", ..),
      Token(kind: "Name", value: "add", ..),
      Token(kind: "Punct", value: "(", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Punct", value: ":", ..),
      Token(kind: "Name", value: "Int", ..),
      Token(kind: "Punct", value: ",", ..),
      Token(kind: "Name", value: "y", ..),
      Token(kind: "Punct", value: ":", ..),
      Token(kind: "Name", value: "Int", ..),
      Token(kind: "Punct", value: ")", ..),
      Token(kind: "Op", value: "->", ..),
      Token(kind: "Name", value: "Int", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Name", value: "x", ..),
      Token(kind: "Op", value: "+", ..),
      Token(kind: "Name", value: "y", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

// ============================================================================
// Edge cases for Tao-specific features
// ============================================================================

pub fn tokenize_double_dash_is_two_operators_not_comment_test() {
  // "--" should be two Op tokens, not a comment (that requires "//")
  let tokens = tokenize("--")
  assert list.length(tokens) == 3
  assert case tokens {
    [Token(kind: "Op", value: "-", ..), Token(kind: "Op", value: "-", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_arrow_separated_by_space_test() {
  // "->" separated as "- >" should be two Op tokens
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

pub fn tokenize_consecutive_multi_char_operators_test() {
  // "-> >" should produce "->", ">", Eof
  let tokens = tokenize("-> >")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Op", value: "->", ..),
      Token(kind: "Op", value: ">", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_underscore_equals_test() {
  // "_" is a Name, "=" is Punct
  let tokens = tokenize("_=")
  assert case tokens {
    [
      Token(kind: "Name", value: "_", ..),
      Token(kind: "Punct", value: "=", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_all_keywords_as_name_tokens_test() {
  // Verify all Tao keywords are recognized
  let all_keywords = [
    "in", "fn", "rec", "with", "case", "if", "then", "else",
    "pub", "import", "type", "match", "let", "mut", "as",
    "true", "false", "for", "while", "loop", "break",
    "continue", "return", "and", "or", "not",
  ]
  let all_keyword_tokens = all_keywords
  |> list.map(fn(kw) { tokenize(kw) })
  |> list.all(fn(tokens) {
    case tokens {
      [Token(kind: "Keyword", value: _kw, ..), Token(kind: "Eof", ..)] -> True
      _ -> False
    }
  })
  assert all_keyword_tokens == True
}

pub fn tokenize_pipe_and_ampersand_are_punct_not_multi_op_test() {
  // "|" and "&" should be Punct (single char), not multi-char operators
  let pipe_tokens = tokenize("|")
  let amp_tokens = tokenize("&")
  assert case pipe_tokens {
    [Token(kind: "Punct", value: "|", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
  assert case amp_tokens {
    [Token(kind: "Punct", value: "&", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}

pub fn tokenize_bare_dot_following_name_test() {
  // "foo ." should be Name + Punct("."
  let tokens = tokenize("foo .")
  assert list.length(tokens) == 3
  assert case tokens {
    [
      Token(kind: "Name", value: "foo", ..),
      Token(kind: "Punct", value: ".", ..),
      Token(kind: "Eof", ..),
    ] -> True
    _ -> False
  }
}

pub fn tokenize_exclamation_and_equals_as_operator_test() {
  // "!=" is a multi-char operator token
  let tokens = tokenize("!=")
  assert case tokens {
    [Token(kind: "Op", value: "!=", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
