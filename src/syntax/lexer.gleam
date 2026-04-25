/// Tokenizer (Lexer)
///
/// Converts source code strings into a list of tokens with span tracking.
/// This is the first phase of the compiler pipeline.
///
/// Token kinds:
///   - `Integer`  - integer literals (e.g. 42, 0, -1)
///   - `Float`    - float literals (e.g. 3.14, .5)
///   - `String`   - string literals with escape sequences
///   - `Name`     - identifiers and keywords (e.g. let, fn, x)
///   - `Op`       - operators (e.g. +, ==, ->, ..)
///   - `Punct`    - punctuation (e.g. (, ), {, }, ;)
///   - `Comment`  - ignored comments (both // and /* */)
///   - `Eof`      - end of file marker

import gleam/list
import gleam/string
import gleam/option.{type Option, Some, None}
import syntax/span.{Span, type Span}

/// Token produced by the lexer.
///
/// Each token carries its kind, value, and the span (source location)
/// where it was found.
pub type Token {
  Token(
    kind: String,
    value: String,
    span: Span,
  )
}

/// Tokenize a source string into a list of tokens.
///
/// Skips whitespace and comments. Produces an `Eof` token at the end.
/// All spans use the filename `""` — use `tokenize_with_filename`
/// to attach a real filename.
///
/// # Example
///
/// ```gleam
/// import syntax/lexer.{tokenize}
/// import syntax/lexer.{Token}
///
/// let tokens = tokenize("let x = 42")
/// // Produces: [Token(kind: "Keyword", value: "let", ..),
/// //           Token(kind: "Name", value: "x", ..),
/// //           Token(kind: "Op", value: "=", ..),
/// //           Token(kind: "Integer", value: "42", ..),
/// //           Token(kind: "Eof", value: "", ..)]
/// ```
pub fn tokenize(source: String) -> List(Token) {
  tokenize_with_filename(source, "")
}

/// Tokenize with an explicit filename for span tracking.
///
/// # Example
///
/// ```gleam
/// import syntax/lexer.{tokenize_with_filename}
///
/// let tokens = tokenize_with_filename("let x = 42", "main.tao")
/// ```
pub fn tokenize_with_filename(source: String, filename: String) -> List(Token) {
  let state = State(
    source: source,
    filename: filename,
    pos: 0,
    line: 1,
    col: 1,
    tokens: [],
  )
  tokenize_loop(state) |> fn(s) { list.reverse(s.tokens) }
}

/// Internal lexer state.
type State {
  State(
    source: String,
    filename: String,
    pos: Int,
    line: Int,
    col: Int,
    tokens: List(Token),
  )
}

/// Character classification helpers.

/// Check if a character is a digit (0-9).
fn is_digit(char: String) -> Bool {
  case char {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

/// Check if a character is valid in an identifier (a-z, A-Z, 0-9, _).
fn is_ident_char(char: String) -> Bool {
  case string.to_graphemes(char) {
    [ch] -> is_alpha(ch) || is_digit(ch) || ch == "_"
    _ -> False
  }
}

/// Check if a character is a letter (a-z, A-Z).
fn is_alpha(char: String) -> Bool {
  case char {
    "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j"
    | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t"
    | "u" | "v" | "w" | "x" | "y" | "z" -> True
    "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J"
    | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T"
    | "U" | "V" | "W" | "X" | "Y" | "Z" -> True
    _ -> False
  }
}

/// Tokenize the main loop.
fn tokenize_loop(state: State) -> State {
  case peek_char(state) {
    "" -> eof(state)
    " " | "\t" | "\r" -> skip_whitespace(state) |> tokenize_loop
    "\n" -> handle_newline(state) |> tokenize_loop
    "/" -> {
      case peek_next(state) {
        Some("/") -> skip_line_comment(state) |> tokenize_loop
        Some("*") -> skip_block_comment(state) |> tokenize_loop
        _ -> tokenize_op(state) |> tokenize_loop
      }
    }
    "\"" -> tokenize_string(state) |> tokenize_loop
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
      tokenize_number(state) |> tokenize_loop
    "_" -> tokenize_op(state) |> tokenize_loop
    "λ" -> tokenize_lambda(state) |> tokenize_loop
    c -> case is_ident_char(c) {
      True -> tokenize_name(state) |> tokenize_loop
      False -> tokenize_op(state) |> tokenize_loop
    }
  }
}

/// Peek at the character at the current position.
///
/// Returns the character and the current state.
fn peek_char(state: State) -> String {
  case state.pos < string.length(state.source) {
    True -> string.slice(state.source, state.pos, 1)
    False -> ""
  }
}

/// Peek at the next character (one position ahead).
fn peek_next(state: State) -> Option(String) {
  case state.pos + 1 < string.length(state.source) {
    True -> Some(string.slice(state.source, state.pos + 1, 1))
    False -> None
  }
}

/// Advance the lexer by one character, updating line/column tracking.
fn advance(state: State) -> State {
  case peek_char(state) {
    "\n" -> State(
      ..state,
      pos: state.pos + 1,
      line: state.line + 1,
      col: 1,
    )
    _ -> State(
      ..state,
      pos: state.pos + 1,
      col: state.col + 1,
    )
  }
}

fn skip_whitespace(state: State) -> State {
  case peek_char(state) {
    " " | "\t" | "\r" -> advance(state) |> skip_whitespace
    _ -> state
  }
}

fn handle_newline(state: State) -> State {
  advance(state)
}

fn skip_line_comment(state: State) -> State {
  case peek_char(state) {
    "\n" | "" -> state
    _ -> advance(state) |> skip_line_comment
  }
}

fn skip_block_comment(state: State) -> State {
  case peek_char(state) {
    "" -> state
    "*" -> {
      case peek_next(state) {
        Some("/") -> advance(state) |> advance
        _ -> advance(state) |> skip_block_comment
      }
    }
    "\n" -> {
      let state = advance(state)
      State(..state, line: state.line + 1, col: 1) |> skip_block_comment
    }
    _ -> advance(state) |> skip_block_comment
  }
}

/// Tokenize a string literal with escape sequence support.
fn tokenize_string(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let state = advance(state) // skip opening "
  let #(content, state) = read_string_content(state, "")
  let state = advance(state) // skip closing "
  let token = Token(
    kind: "String",
    value: content,
    span: Span(state.filename, start_line, start_col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}

fn read_string_content(state: State, acc: String) -> #(String, State) {
  case peek_char(state) {
    "" | "\"" -> #(acc, state)
    "\\" -> {
      let state = advance(state)
      case peek_char(state) {
        "n" -> read_string_content(advance(state), acc <> "\n")
        "t" -> read_string_content(advance(state), acc <> "\t")
        "\"" -> read_string_content(advance(state), acc <> "\"")
        "\\" -> read_string_content(advance(state), acc <> "\\")
        _ -> read_string_content(state, acc)
      }
    }
    c -> read_string_content(advance(state), acc <> c)
  }
}

/// Tokenize a number literal (integer or float).
fn tokenize_number(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let #(digits, state) = read_digits(state, "")

  // Check for decimal point followed by digits (float literal)
  case peek_char(state) {
    "." -> {
      case peek_next(state) {
        Some(next) -> case is_digit(next) {
          True -> {
            // Float literal: consume the ".", then read fractional digits
            let state = advance(state) // consume "."
            let #(frac_digits, state) = read_digits(state, "")
            let value = digits <> "." <> frac_digits
            let token = Token(
              kind: "Float",
              value: value,
              span: Span(state.filename, start_line, start_col, state.line, state.col),
            )
            State(..state, tokens: [token, ..state.tokens])
          }
          False -> {
            // Just a number followed by a bare dot — tokenize as integer
            let token = Token(
              kind: "Integer",
              value: digits,
              span: Span(state.filename, start_line, start_col, state.line, state.col),
            )
            State(..state, tokens: [token, ..state.tokens])
          }
        }
        None -> {
          // Just a number followed by a bare dot — tokenize as integer
          let token = Token(
            kind: "Integer",
            value: digits,
            span: Span(state.filename, start_line, start_col, state.line, state.col),
          )
          State(..state, tokens: [token, ..state.tokens])
        }
      }
    }
    _ -> {
      let token = Token(
        kind: "Integer",
        value: digits,
        span: Span(state.filename, start_line, start_col, state.line, state.col),
      )
      State(..state, tokens: [token, ..state.tokens])
    }
  }
}

fn read_digits(state: State, acc: String) -> #(String, State) {
  case peek_char(state) {
    c -> case is_digit(c) {
      True -> read_digits(advance(state), acc <> c)
      False -> #(acc, state)
    }
  }
}

/// Tokenize an identifier or keyword.
fn tokenize_name(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let #(chars, state) = read_ident_chars(state, [])
  let value = string.join(chars, "")
  let kind = get_name_kind(value)
  let token = Token(
    kind: kind,
    value: value,
    span: Span(state.filename, start_line, start_col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}

fn get_name_kind(value: String) -> String {
  case value {
    "in"
    | "fn"
    | "rec"
    | "with"
    | "case"
    | "if"
    | "then"
    | "else"
    | "pub"
    | "import"
    | "type"
    | "match"
    | "let"
    | "mut"
    | "as"
    | "true"
    | "false"
    | "for"
    | "while"
    | "loop"
    | "break"
    | "continue"
    | "return"
    | "and"
    | "or"
    | "not" -> "Keyword"
    _ -> "Name"
  }
}

fn read_ident_chars(state: State, acc: List(String)) -> #(List(String), State) {
  case peek_char(state) {
    c -> case is_ident_char(c) {
      True -> read_ident_chars(advance(state), [c, ..acc])
      False -> #(list.reverse(acc), state)
    }
  }
}

/// Tokenize the λ (lambda) symbol.
fn tokenize_lambda(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let state = advance(state)
  let token = Token(
    kind: "Lambda",
    value: "λ",
    span: Span(state.filename, start_line, start_col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}

/// Tokenize operators and punctuation.
///
/// Handles both single-character and multi-character operators.
/// Multi-character operators are checked first (longest match).
fn tokenize_op(state: State) -> State {
  case peek_char(state) {
    "" -> state
    char -> {
      let start_line = state.line
      let start_col = state.col
      let span = Span(state.filename, start_line, start_col, state.line, state.col)

      // Try multi-character operators first
      case try_multi_char_op(char, state) {
        Ok(#(value, new_state)) -> {
          let token = Token(kind: "Op", value: value, span: span)
          State(..new_state, tokens: [token, ..new_state.tokens])
        }
        Error(_) -> {
          // Handle single-character punctuation
          case char {
            "(" -> single_punct(state, "(", span)
            ")" -> single_punct(state, ")", span)
            "{" -> single_punct(state, "{", span)
            "}" -> single_punct(state, "}", span)
            "[" -> single_punct(state, "[", span)
            "]" -> single_punct(state, "]", span)
            "," -> single_punct(state, ",", span)
            ";" -> single_punct(state, ";", span)
            ":" -> single_punct(state, ":", span)
            "=" -> single_punct(state, "=", span)
            "!" -> single_punct(state, "!", span)
            "|" -> single_punct(state, "|", span)
            "&" -> single_punct(state, "&", span)
            "." -> single_punct(state, ".", span)
            _ -> single_op(state, char, span)
          }
        }
      }
    }
  }
}

/// Try to match a multi-character operator.
/// Returns Ok(#(operator_value, new_state)) if found, Error otherwise.
fn try_multi_char_op(char: String, state: State) -> Result(#(String, State), Nil) {
  case peek_next(state) {
    Some("=") -> case char {
      "=" | "!" | "<" | ">" -> Ok(#(char <> "=", advance(state) |> advance))
      _ -> Error(Nil)
    }
    Some(">") -> case char {
      "-" -> Ok(#("->", advance(state) |> advance))
      _ -> Error(Nil)
    }
    Some("-") -> case char {
      "<" -> Ok(#("<-", advance(state) |> advance))
      _ -> Error(Nil)
    }
    Some("|") -> case char {
      "|" -> Ok(#("||", advance(state) |> advance))
      _ -> Error(Nil)
    }
    Some("&") -> case char {
      "&" -> Ok(#("&&", advance(state) |> advance))
      _ -> Error(Nil)
    }
    Some(".") -> case char {
      "." -> Ok(#("..", advance(state) |> advance))
      _ -> Error(Nil)
    }
    _ -> Error(Nil)
  }
}

/// Handle a single-character operator/punctuation token.
fn single_op(state: State, char: String, span: Span) -> State {
  let token = Token(kind: "Op", value: char, span: span)
  State(..advance(state), tokens: [token, ..state.tokens])
}

/// Handle a single-character punctuation token.
fn single_punct(state: State, punct: String, span: Span) -> State {
  let token = Token(kind: "Punct", value: punct, span: span)
  State(..advance(state), tokens: [token, ..state.tokens])
}

fn eof(state: State) -> State {
  let token = Token(
    kind: "Eof",
    value: "",
    span: Span(state.filename, state.line, state.col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}
