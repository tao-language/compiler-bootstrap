/// Language-agnostic Lexer (Base)
///
/// Provides fundamental tokenization shared by all languages:
/// - Whitespace and comment skipping
/// - String literals with escape sequences
/// - Number literals (integer and float)
/// - Identifier tokenization (returns raw "Name" for all identifiers)
/// - Single character handling
///
/// Language-specific extensions (keywords, multi-char operators,
/// lambda symbol, etc.) are provided by the `tao/lexer` module
/// which composes on top of this base.

import gleam/list
import gleam/string
import gleam/option.{type Option, Some, None}
import syntax/span.{Span, type Span}

/// Token produced by the lexer.
///
/// Each token carries its kind, value, and the span (source location)
/// where it was found.
///
/// Token kinds produced by this base lexer:
///   - `Integer`  - integer literals (e.g. 42, 0)
///   - `Float`    - float literals (e.g. 3.14, .5)
///   - `String`   - string literals with escape sequences
///   - `Name`     - identifiers (e.g. x, foo, my_var)
///   - `Op`       - operators (e.g. +, -, *, /, <, >, =, etc.)
///   - `Punct`    - punctuation (e.g. (, ), {, }, [, ], ,, ;, :, |, &, .)
///   - `Comment`  - ignored comments (both // and /* */)
///   - `Eof`      - end of file marker
///
/// Note: Keywords are returned as `Name` tokens by the base lexer.
/// Language-specific keyword detection is performed by the grammar
/// layer (see `grammar.kw` pattern).
pub type Token {
  Token(
    kind: String,
    value: String,
    span: Span,
  )
}

/// Internal lexer state.
///
/// Exported for use by language-specific lexers that extend the base.
pub type State {
  State(
    source: String,
    filename: String,
    pos: Int,
    line: Int,
    col: Int,
    tokens: List(Token),
  )
}

/// Tokenize a source string into a list of tokens.
///
/// Skips whitespace and comments. Produces an `Eof` token at the end.
/// All spans use the filename `""` — use `tokenize_with_filename`
/// to attach a real filename.
pub fn tokenize(source: String) -> List(Token) {
  tokenize_with_filename(source, "")
}

/// Tokenize with an explicit filename for span tracking.
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

// ==========================================================================
// Internal helper functions (exported for use by language-specific lexers)
// ==========================================================================

/// Check if a character is a digit (0-9).
pub fn is_digit(char: String) -> Bool {
  case char {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

/// Check if a character is valid in an identifier (a-z, A-Z, 0-9, _).
pub fn is_ident_char(char: String) -> Bool {
  case string.to_graphemes(char) {
    [ch] -> is_alpha(ch) || is_digit(ch) || ch == "_"
    _ -> False
  }
}

/// Check if a character is a letter (a-z, A-Z).
pub fn is_alpha(char: String) -> Bool {
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

/// Peek at the character at the current position.
pub fn peek_char(state: State) -> String {
  case state.pos < string.length(state.source) {
    True -> string.slice(state.source, state.pos, 1)
    False -> ""
  }
}

/// Peek at the next character (one position ahead).
pub fn peek_next(state: State) -> Option(String) {
  case state.pos + 1 < string.length(state.source) {
    True -> Some(string.slice(state.source, state.pos + 1, 1))
    False -> None
  }
}

/// Advance the lexer by one character, updating line/column tracking.
pub fn advance(state: State) -> State {
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

/// Skip whitespace characters (space, tab, carriage return).
pub fn skip_whitespace(state: State) -> State {
  case peek_char(state) {
    " " | "\t" | "\r" -> advance(state) |> skip_whitespace
    _ -> state
  }
}

/// Handle a newline character.
pub fn handle_newline(state: State) -> State {
  advance(state)
}

/// Skip a line comment (//).
pub fn skip_line_comment(state: State) -> State {
  case peek_char(state) {
    "\n" | "" -> state
    _ -> advance(state) |> skip_line_comment
  }
}

/// Skip a block comment (/* ... */).
pub fn skip_block_comment(state: State) -> State {
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
pub fn tokenize_string(state: State) -> State {
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
///
/// This is generic: it detects the presence of a decimal point to
/// distinguish integers from floats.
pub fn tokenize_number(state: State) -> State {
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

/// Tokenize an identifier.
///
/// Returns a `Name` token with the raw identifier value.
/// Language-specific keyword detection (e.g., "let", "fn", "true")
/// is performed by the grammar layer via the `kw` pattern.
pub fn tokenize_identifier(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let #(chars, state) = read_ident_chars(state, [])
  let value = string.join(chars, "")
  let token = Token(
    kind: "Name",
    value: value,
    span: Span(state.filename, start_line, start_col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}

pub fn read_ident_chars(state: State, acc: List(String)) -> #(List(String), State) {
  case peek_char(state) {
    c -> case is_ident_char(c) {
      True -> read_ident_chars(advance(state), [c, ..acc])
      False -> #(list.reverse(acc), state)
    }
  }
}

/// Handle a single-character operator token.
pub fn single_op(state: State, char: String, span: Span) -> State {
  let token = Token(kind: "Op", value: char, span: span)
  State(..advance(state), tokens: [token, ..state.tokens])
}

/// Handle a single-character punctuation token.
pub fn single_punct(state: State, punct: String, span: Span) -> State {
  let token = Token(kind: "Punct", value: punct, span: span)
  State(..advance(state), tokens: [token, ..state.tokens])
}

/// End-of-file marker token.
pub fn eof(state: State) -> State {
  let token = Token(
    kind: "Eof",
    value: "",
    span: Span(state.filename, state.line, state.col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}

// ==========================================================================
// Internal functions (NOT exported — used only by the base lexer itself)
// ==========================================================================

/// Tokenize the main loop (internal, not exported).
fn tokenize_loop(state: State) -> State {
  case peek_char(state) {
    "" -> eof(state)
    " " | "\t" | "\r" -> skip_whitespace(state) |> tokenize_loop
    "\n" -> handle_newline(state) |> tokenize_loop
    "/" -> {
      case peek_next(state) {
        Some("/") -> skip_line_comment(state) |> tokenize_loop
        Some("*") -> skip_block_comment(state) |> tokenize_loop
        _ -> tokenize_single_char(state) |> tokenize_loop
      }
    }
    "\"" -> tokenize_string(state) |> tokenize_loop
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
      tokenize_number(state) |> tokenize_loop
    c -> case is_ident_char(c) {
      True -> tokenize_identifier(state) |> tokenize_loop
      False -> tokenize_single_char(state) |> tokenize_loop
    }
  }
}

/// Tokenize a single character (operator or punctuation).
fn tokenize_single_char(state: State) -> State {
  case peek_char(state) {
    "" -> state
    char -> {
      let start_line = state.line
      let start_col = state.col
      let span = Span(state.filename, start_line, start_col, state.line, state.col)

      // Punctuation — structural characters used by all languages
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
