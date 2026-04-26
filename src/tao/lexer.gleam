/// Tao Lexer
///
/// Extends the base lexer with Tao-specific constructs:
/// - Keywords (let, fn, true, false, etc.)
/// - Multi-character operators (->, ==, !=, &&, ||, .., etc.)
/// - Lambda symbol (λ)
///
/// This module provides the complete tokenizer for Tao source files.
/// It is the first phase of the Tao compiler pipeline.

import gleam/list
import gleam/string
import gleam/option.{Some, None}
import syntax/base_lexer as bl
import syntax/span.{Span}
import tao/language_config.{is_keyword, try_multi_char_op, lambda_symbol}

/// Tokenize a Tao source string into a list of tokens.
///
/// Unlike the base lexer, this:
/// - Classifies keywords as "Keyword" tokens
/// - Detects multi-character operators (->, ==, etc.)
/// - Tokenizes the λ symbol as "Lambda"
pub fn tokenize(source: String) -> List(bl.Token) {
  tokenize_with_filename(source, "")
}

/// Tokenize a Tao source string with explicit filename.
pub fn tokenize_with_filename(source: String, filename: String) -> List(bl.Token) {
  let state = bl.State(
    source: source,
    filename: filename,
    pos: 0,
    line: 1,
    col: 1,
    tokens: [],
  )
  tokenize_loop(state) |> fn(s) { list.reverse(s.tokens) }
}

/// Tokenize the main loop.
///
/// Same structure as the base lexer, with Tao-specific additions:
/// - λ symbol → "Lambda" token
/// - Keywords detected during identifier tokenization
/// - Multi-character operators checked during single-char handling
fn tokenize_loop(state: bl.State) -> bl.State {
  case bl.peek_char(state) {
    "" -> bl.eof(state)
    " " | "\t" | "\r" -> bl.skip_whitespace(state) |> tokenize_loop
    "\n" -> bl.handle_newline(state) |> tokenize_loop
    "/" -> {
      case bl.peek_next(state) {
        Some("/") -> bl.skip_line_comment(state) |> tokenize_loop
        Some("*") -> bl.skip_block_comment(state) |> tokenize_loop
        _ -> tokenize_op(state) |> tokenize_loop
      }
    }
    "\"" -> bl.tokenize_string(state) |> tokenize_loop
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
      bl.tokenize_number(state) |> tokenize_loop
    char -> case char == lambda_symbol() {
      True -> tokenize_lambda(state) |> tokenize_loop
      False -> case bl.is_ident_char(char) {
        True -> tokenize_name(state) |> tokenize_loop
        False -> tokenize_op(state) |> tokenize_loop
      }
    }
  }
}

/// Tokenize a lambda (λ) symbol.
fn tokenize_lambda(state: bl.State) -> bl.State {
  let start_line = state.line
  let start_col = state.col
  let new_state = bl.advance(state)
  let token = bl.Token(
    kind: "Lambda",
    value: "λ",
    span: Span(new_state.filename, start_line, start_col, new_state.line, new_state.col),
  )
  bl.State(..new_state, tokens: [token, ..new_state.tokens])
}

/// Tokenize an identifier or keyword.
///
/// Returns "Keyword" if the identifier is a Tao keyword,
/// otherwise "Name".
fn tokenize_name(state: bl.State) -> bl.State {
  let start_line = state.line
  let start_col = state.col
  let chars = bl.read_ident_chars(state, [])
  let value = string.join(chars.0, "")
  let kind = get_name_kind(value)
  let token = bl.Token(
    kind: kind,
    value: value,
    span: Span(chars.1.filename, start_line, start_col, chars.1.line, chars.1.col),
  )
  bl.State(..chars.1, tokens: [token, ..chars.1.tokens])
}

/// Determine if an identifier is a keyword.
fn get_name_kind(value: String) -> String {
  case is_keyword(value) {
    True -> "Keyword"
    False -> "Name"
  }
}

/// Tokenize operators and punctuation.
///
/// Handles both single-character operators/punctuation and
/// multi-character operators (checked first via longest match).
fn tokenize_op(state: bl.State) -> bl.State {
  case bl.peek_char(state) {
    "" -> state
    char -> {
      let start_line = state.line
      let start_col = state.col
      let span = Span(state.filename, start_line, start_col, state.line, state.col)

      // Try multi-character operators first
      case try_multi_char_ops(char, state) {
        Ok(#(value, new_state)) -> {
          let token = bl.Token(kind: "Op", value: value, span: span)
          bl.State(..new_state, tokens: [token, ..new_state.tokens])
        }
        Error(_) -> {
          // Handle single-character punctuation
          case char {
            "(" -> bl.single_punct(state, "(", span)
            ")" -> bl.single_punct(state, ")", span)
            "{" -> bl.single_punct(state, "{", span)
            "}" -> bl.single_punct(state, "}", span)
            "[" -> bl.single_punct(state, "[", span)
            "]" -> bl.single_punct(state, "]", span)
            "," -> bl.single_punct(state, ",", span)
            ";" -> bl.single_punct(state, ";", span)
            ":" -> bl.single_punct(state, ":", span)
            "=" -> bl.single_punct(state, "=", span)
            "!" -> bl.single_punct(state, "!", span)
            "|" -> bl.single_punct(state, "|", span)
            "&" -> bl.single_punct(state, "&", span)
            "." -> bl.single_punct(state, ".", span)
            _ -> bl.single_op(state, char, span)
          }
        }
      }
    }
  }
}

/// Try to match a multi-character operator.
///
/// Returns Ok(#(operator_value, new_state)) if found, Error otherwise.
/// The new_state has already been advanced by 2 characters.
fn try_multi_char_ops(char: String, state: bl.State) -> Result(#(String, bl.State), Nil) {
  case bl.peek_next(state) {
    Some(second) -> {
      case try_multi_char_op(char, second) {
        Some(combined) -> {
          let new_state = bl.advance(state) |> bl.advance
          Ok(#(combined, new_state))
        }
        None -> Error(Nil)
      }
    }
    None -> Error(Nil)
  }
}
