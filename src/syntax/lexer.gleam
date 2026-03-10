// ============================================================================
// LEXER - Tokenizer
// ============================================================================
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

pub type Token {
  Token(
    kind: String,
    value: String,
    start: Int,       // Character offset (0-based)
    end: Int,         // Character offset (0-based)
    line: Int,        // Line number (1-based)
    column: Int,      // Column number (1-based)
  )
}

pub type Position {
  Position(offset: Int, line: Int, column: Int)
}

type LexerState {
  LexerState(
    source: String,
    pos: Int,
    line: Int,
    column: Int,
    tokens: List(Token),
  )
}

pub fn tokenize(source: String) -> List(Token) {
  let state = LexerState(source: source, pos: 0, line: 1, column: 1, tokens: [])
  tokenize_loop(state) |> fn(s) { list.reverse(s.tokens) }
}

fn tokenize_loop(state: LexerState) -> LexerState {
  case peek_char(state) {
    None -> state
    Some(char) -> {
      case char {
        " " | "\t" | "\r" -> skip_whitespace(state) |> tokenize_loop
        "\n" -> handle_newline(state) |> tokenize_loop
        "/" -> {
          case peek_next_char(state) {
            Some("/") -> skip_line_comment(state) |> tokenize_loop
            Some("*") -> skip_block_comment(state) |> tokenize_loop
            _ -> tokenize_operator(state) |> tokenize_loop
          }
        }
        "\"" -> tokenize_string(state) |> tokenize_loop
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
          tokenize_number(state) |> tokenize_loop
        "?" -> tokenize_question(state) |> tokenize_loop
        "a"
        | "b"
        | "c"
        | "d"
        | "e"
        | "f"
        | "g"
        | "h"
        | "i"
        | "j"
        | "k"
        | "l"
        | "m"
        | "n"
        | "o"
        | "p"
        | "q"
        | "r"
        | "s"
        | "t"
        | "u"
        | "v"
        | "w"
        | "x"
        | "y"
        | "z"
        | "A"
        | "B"
        | "C"
        | "D"
        | "E"
        | "F"
        | "G"
        | "H"
        | "I"
        | "J"
        | "K"
        | "L"
        | "M"
        | "N"
        | "O"
        | "P"
        | "Q"
        | "R"
        | "S"
        | "T"
        | "U"
        | "V"
        | "W"
        | "X"
        | "Y"
        | "Z"
        | "_" -> tokenize_ident(state) |> tokenize_loop
        "λ" -> tokenize_lambda(state) |> tokenize_loop
        _ -> tokenize_operator(state) |> tokenize_loop
      }
    }
  }
}

fn skip_whitespace(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some(c) if c == " " || c == "\t" || c == "\r" ->
      advance(state) |> skip_whitespace
    _ -> state
  }
}

fn handle_newline(state: LexerState) -> LexerState {
  advance(state)
}

fn skip_line_comment(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some("\n") | None -> state
    Some(_) -> advance(state) |> skip_line_comment
  }
}

fn skip_block_comment(state: LexerState) -> LexerState {
  case peek_char(state) {
    None -> state
    Some("*") -> {
      case peek_next_char(state) {
        Some("/") -> advance(state) |> advance
        _ -> advance(state) |> skip_block_comment
      }
    }
    Some("\n") -> {
      let state = advance(state)
      LexerState(..state, line: state.line + 1, column: 1) |> skip_block_comment
    }
    Some(_) -> advance(state) |> skip_block_comment
  }
}

fn tokenize_string(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column
  let state = advance(state)  // Skip opening quote
  let #(content, state) = read_string_content(state, "")
  let state = advance(state)  // Skip closing quote
  let end_pos = state.pos
  let token =
    Token(kind: "String", value: content, start: start_pos, end: end_pos, line: start_line, column: start_column)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn read_string_content(state: LexerState, acc: String) -> #(String, LexerState) {
  case peek_char(state) {
    None | Some("\"") -> #(acc, state)
    Some("\\") -> {
      let state = advance(state)
      case peek_char(state) {
        Some("n") -> read_string_content(advance(state), acc <> "\n")
        Some("t") -> read_string_content(advance(state), acc <> "\t")
        Some("\"") -> read_string_content(advance(state), acc <> "\"")
        Some("\\") -> read_string_content(advance(state), acc <> "\\")
        _ -> read_string_content(state, acc)
      }
    }
    Some(char) -> read_string_content(advance(state), acc <> char)
  }
}

fn tokenize_number(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column
  let #(digits, state) = read_digits(state, "")
  let end_pos = state.pos
  let token =
    Token(kind: "Number", value: digits, start: start_pos, end: end_pos, line: start_line, column: start_column)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn read_digits(state: LexerState, acc: String) -> #(String, LexerState) {
  case peek_char(state) {
    Some(d)
      if d == "0"
      || d == "1"
      || d == "2"
      || d == "3"
      || d == "4"
      || d == "5"
      || d == "6"
      || d == "7"
      || d == "8"
      || d == "9"
    -> read_digits(advance(state), acc <> d)
    _ -> #(acc, state)
  }
}

fn tokenize_ident(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column
  let #(chars, state) = read_ident_chars(state, [])
  let value = string.concat(chars)
  let kind = get_keyword_kind(value)
  let end_pos = state.pos
  let token = Token(kind: kind, value: value, start: start_pos, end: end_pos, line: start_line, column: start_column)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn get_keyword_kind(value: String) -> String {
  case value {
    "let"
    | "in"
    | "fn"
    | "match"
    | "with"
    | "case"
    | "if"
    | "then"
    | "else"
    | "comptime"
    | "pub"
    | "import"
    | "type"
    | "opaque" -> "Keyword"
    _ -> "Ident"
  }
}

fn read_ident_chars(
  state: LexerState,
  acc: List(String),
) -> #(List(String), LexerState) {
  case peek_char(state) {
    Some(c) -> {
      case is_ident_char(c) {
        True -> read_ident_chars(advance(state), [c, ..acc])
        False -> #(list.reverse(acc), state)
      }
    }
    None -> #(list.reverse(acc), state)
  }
}

fn is_ident_char(char: String) -> Bool {
  case char {
    "a"
    | "b"
    | "c"
    | "d"
    | "e"
    | "f"
    | "g"
    | "h"
    | "i"
    | "j"
    | "k"
    | "l"
    | "m"
    | "n"
    | "o"
    | "p"
    | "q"
    | "r"
    | "s"
    | "t"
    | "u"
    | "v"
    | "w"
    | "x"
    | "y"
    | "z"
    | "A"
    | "B"
    | "C"
    | "D"
    | "E"
    | "F"
    | "G"
    | "H"
    | "I"
    | "J"
    | "K"
    | "L"
    | "M"
    | "N"
    | "O"
    | "P"
    | "Q"
    | "R"
    | "S"
    | "T"
    | "U"
    | "V"
    | "W"
    | "X"
    | "Y"
    | "Z"
    | "0"
    | "1"
    | "2"
    | "3"
    | "4"
    | "5"
    | "6"
    | "7"
    | "8"
    | "9"
    | "_"
    | "λ" -> True
    _ -> False
  }
}

fn tokenize_lambda(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column
  let state = advance(state)
  let end_pos = state.pos
  let token = Token(kind: "Lambda", value: "λ", start: start_pos, end: end_pos, line: start_line, column: start_column)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn tokenize_question(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column
  let state = advance(state)
  let end_pos = state.pos
  let token = Token(kind: "Question", value: "?", start: start_pos, end: end_pos, line: start_line, column: start_column)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn tokenize_operator(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some(char) -> {
      let start_pos = state.pos
      let start_line = state.line
      let start_column = state.column

      // Check for % keywords first (%match, %call, %comptime)
      case char == "%" {
        True -> tokenize_percent_keyword(state)
        False -> tokenize_other_operator(state, start_pos, start_line, start_column)
      }
    }
    None -> state
  }
}

fn tokenize_percent_keyword(state: LexerState) -> LexerState {
  let start_pos = state.pos
  let start_line = state.line
  let start_column = state.column

  // Check what follows % by looking at the next characters
  // %match = 6 chars, %call = 5 chars, %comptime = 9 chars
  case peek_n_chars(state, 6) {  // Check for "%match"
    "%match" -> {
      // %match
      let state = advance(state)  // %
      let state = advance_n(state, 5)  // match
      let end_pos = state.pos
      let token = Token(kind: "PercentMatch", value: "%match", start: start_pos, end: end_pos, line: start_line, column: start_column)
      LexerState(..state, tokens: [token, ..state.tokens])
    }
    _ -> {
      case peek_n_chars(state, 5) {  // Check for "%call"
        "%call" -> {
          // %call
          let state = advance(state)  // %
          let state = advance_n(state, 4)  // call
          let end_pos = state.pos
          let token = Token(kind: "PercentCall", value: "%call", start: start_pos, end: end_pos, line: start_line, column: start_column)
          LexerState(..state, tokens: [token, ..state.tokens])
        }
        _ -> {
          case peek_n_chars(state, 9) {  // Check for "%comptime"
            "%comptime" -> {
              // %comptime
              let state = advance(state)  // %
              let state = advance_n(state, 8)  // comptime
              let end_pos = state.pos
              let token = Token(kind: "PercentComptime", value: "%comptime", start: start_pos, end: end_pos, line: start_line, column: start_column)
              LexerState(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              // Just %
              let state = advance(state)
              let end_pos = state.pos
              let token = Token(kind: "Percent", value: "%", start: start_pos, end: end_pos, line: start_line, column: start_column)
              LexerState(..state, tokens: [token, ..state.tokens])
            }
          }
        }
      }
    }
  }
}

fn peek_n_chars(state: LexerState, n: Int) -> String {
  string.slice(state.source, state.pos, n)
}

fn advance_n(state: LexerState, n: Int) -> LexerState {
  case n <= 0 {
    True -> state
    False -> advance_n(advance(state), n - 1)
  }
}

fn tokenize_other_operator(state: LexerState, start_pos: Int, start_line: Int, start_column: Int) -> LexerState {
  // Check for multi-character operators first
  let next_char = peek_next_char(state)
  case peek_char(state) {
    Some(char) -> {
      case char == "-" && next_char == Some(">") {
        True -> {
          // Arrow: ->
          let state = advance(state) |> advance
          let end_pos = state.pos
          let token = Token(kind: "Arrow", value: "->", start: start_pos, end: end_pos, line: start_line, column: start_column)
          LexerState(..state, tokens: [token, ..state.tokens])
        }
        False -> {
          case char == "=" && next_char == Some("=") {
            True -> {
              // EqualEqual: ==
              let state = advance(state) |> advance
              let end_pos = state.pos
              let token = Token(kind: "EqualEqual", value: "==", start: start_pos, end: end_pos, line: start_line, column: start_column)
              LexerState(..state, tokens: [token, ..state.tokens])
            }
            False -> {
              case char == "!" && next_char == Some("=") {
                True -> {
                  // NotEqual: !=
                  let state = advance(state) |> advance
                  let end_pos = state.pos
                  let token = Token(kind: "NotEqual", value: "!=", start: start_pos, end: end_pos, line: start_line, column: start_column)
                  LexerState(..state, tokens: [token, ..state.tokens])
                }
                False -> {
                  case char == "<" && next_char == Some("-") {
                    True -> {
                      // Arrow2: <-
                      let state = advance(state) |> advance
                      let end_pos = state.pos
                      let token = Token(kind: "Arrow2", value: "<-", start: start_pos, end: end_pos, line: start_line, column: start_column)
                      LexerState(..state, tokens: [token, ..state.tokens])
                    }
                    False -> {
                      // Single character operator
                      let state = advance(state)
                      let end_pos = state.pos
                      let kind = get_operator_kind(char)
                      let token = Token(kind: kind, value: char, start: start_pos, end: end_pos, line: start_line, column: start_column)
                      LexerState(..state, tokens: [token, ..state.tokens])
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    None -> state
  }
}

fn get_operator_kind(char: String) -> String {
  case char {
    "(" -> "LParen"
    ")" -> "RParen"
    "{" -> "LBrace"
    "}" -> "RBrace"
    "[" -> "LBracket"
    "]" -> "RBracket"
    "," -> "Comma"
    "." -> "Dot"
    ";" -> "Semi"
    ":" -> "Colon"
    "=" -> "Equal"
    "$" -> "Dollar"
    "#" -> "Hash"
    "%" -> "Percent"
    "~" -> "Tilde"
    "|" -> "Pipe"
    "_" -> "Underscore"
    "@" -> "At"
    "+"
    | "-"
    | "*"
    | "/"
    | "!"
    | ">"
    | "<"
    | "&"
    | "^" -> "Operator"
    "\\" -> "Backslash"
    _ -> "Operator"
  }
}

fn peek_char(state: LexerState) -> Option(String) {
  case state.pos >= string.length(state.source) {
    True -> None
    False -> Some(string.slice(state.source, state.pos, 1))
  }
}

fn peek_next_char(state: LexerState) -> Option(String) {
  case state.pos + 1 >= string.length(state.source) {
    True -> None
    False -> Some(string.slice(state.source, state.pos + 1, 1))
  }
}

fn advance(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some("\n") ->
      LexerState(..state, pos: state.pos + 1, line: state.line + 1, column: 1)
    Some(_) -> LexerState(..state, pos: state.pos + 1, column: state.column + 1)
    None -> state
  }
}
