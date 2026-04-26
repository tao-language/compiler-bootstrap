/// Language Configuration
///
/// Centralized definitions for Tao language-specific constructs:
/// - Keywords (reserved words that are tokenized as "Keyword")
/// - Multi-character operators (e.g., "->", "==", "&&")
/// - Special symbols (e.g., "λ" for lambda)
///
/// This module is the single source of truth for Tao syntax elements.
/// It is imported by the Tao lexer and the grammar layer.

import gleam/option.{type Option, Some, None}

/// Tao reserved keywords.
///
/// These identifiers are tokenized as "Keyword" instead of "Name".
/// The base lexer returns all identifiers as "Name" tokens;
/// the Tao lexer classifies keywords based on this list.
pub fn keywords() -> List(String) {
  [
    "in",
    "fn",
    "rec",
    "with",
    "case",
    "if",
    "then",
    "else",
    "pub",
    "import",
    "type",
    "match",
    "let",
    "mut",
    "as",
    "true",
    "false",
    "for",
    "while",
    "loop",
    "break",
    "continue",
    "return",
    "and",
    "or",
    "not",
  ]
}

/// Check if an identifier is a Tao keyword.
pub fn is_keyword(name: String) -> Bool {
  is_keyword_loop(keywords(), name)
}

fn is_keyword_loop(keys: List(String), name: String) -> Bool {
  case keys {
    [] -> False
    [first, ..rest] -> {
      case first == name {
        True -> True
        False -> is_keyword_loop(rest, name)
      }
    }
  }
}

/// Multi-character operator definitions.
///
/// Returns a list of #(first_char, second_char, combined) tuples
/// for operators like "->", "==", "&&", etc.
///
/// The lookup iterates through this list to find a match for
/// two consecutive characters.
pub fn multi_char_operators() -> List(#(String, String, String)) {
  [
    #("=", "=", "=="),
    #("!", "=", "!="),
    #("<", "=", "<="),
    #(">", "=", ">="),
    #("-", ">", "->"),
    #("<", "-", "<-"),
    #("|", "|", "||"),
    #("&", "&", "&&"),
    #(".", ".", ".."),
  ]
}

/// Check if two consecutive characters form a multi-char operator.
/// Returns the combined operator string if found, Nil otherwise.
pub fn try_multi_char_op(first: String, second: String) -> Option(String) {
  case multi_char_operators() {
    [] -> None
    [op, ..rest] -> {
      case find_operator(op, first, second) {
        True -> Some(op.2)
        False -> try_multi_char_op_in_rest(rest, first, second)
      }
    }
  }
}

fn find_operator(
  op: #(String, String, String),
  first: String,
  second: String,
) -> Bool {
  op.0 == first && op.1 == second
}

fn try_multi_char_op_in_rest(
  ops: List(#(String, String, String)),
  first: String,
  second: String,
) -> Option(String) {
  case ops {
    [] -> None
    [op, ..rest] -> {
      case find_operator(op, first, second) {
        True -> Some(op.2)
        False -> try_multi_char_op_in_rest(rest, first, second)
      }
    }
  }
}

/// The lambda symbol for Tao.
pub fn lambda_symbol() -> String {
  "λ"
}

/// Check if a character is the lambda symbol.
pub fn is_lambda(char: String) -> Bool {
  char == lambda_symbol()
}
