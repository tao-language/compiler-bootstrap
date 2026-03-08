// ============================================================================
// LEXER - Tokenizer for Grammar System
// ============================================================================

import gleam/list
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

pub type Token {
  Token(
    kind: String,
    value: String,
    start: Position,
    end: Position,
  )
}

pub type Position {
  Position(offset: Int, line: Int, column: Int)
}

pub type LexError {
  LexError(position: Position, message: String)
}

type LexerState {
  LexerState(
    source: String,
    pos: Int,
    line: Int,
    column: Int,
    tokens: List(Token),
    errors: List(LexError),
  )
}

// ============================================================================
// PUBLIC API
// ============================================================================

pub fn tokenize(source: String) -> List(Token) {
  let state = LexerState(
    source: source,
    pos: 0,
    line: 1,
    column: 1,
    tokens: [],
    errors: [],
  )
  tokenize_loop(state) |> fn(s) { list.reverse(s.tokens) }
}

pub fn tokenize_with_errors(source: String) -> #(List(Token), List(LexError)) {
  let state = LexerState(
    source: source,
    pos: 0,
    line: 1,
    column: 1,
    tokens: [],
    errors: [],
  )
  let final_state = tokenize_loop(state)
  #(list.reverse(final_state.tokens), list.reverse(final_state.errors))
}

// ============================================================================
// LEXER LOOP
// ============================================================================

fn tokenize_loop(state: LexerState) -> LexerState {
  case peek_char(state) {
    None -> state
    Some(char) -> {
      case char {
        // Whitespace
        " " | "\t" | "\r" -> skip_whitespace(state) |> tokenize_loop
        "\n" -> handle_newline(state) |> tokenize_loop

        // Comments
        "/" -> {
          case peek_next_char(state) {
            Some("/") -> skip_line_comment(state) |> tokenize_loop
            Some("*") -> skip_block_comment(state) |> tokenize_loop
            _ -> tokenize_operator(state) |> tokenize_loop
          }
        }

        // String literals
        "\"" -> tokenize_string(state) |> tokenize_loop

        // Number literals
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
          tokenize_number(state) |> tokenize_loop

        // Identifiers and keywords
        "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" |
        "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" |
        "y" | "z" | "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" |
        "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" |
        "W" | "X" | "Y" | "Z" | "_" -> tokenize_ident(state) |> tokenize_loop

        // Unicode lambda
        "λ" -> tokenize_lambda(state) |> tokenize_loop

        // Operators and punctuation
        _ -> tokenize_operator(state) |> tokenize_loop
      }
    }
  }
}

fn skip_whitespace(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some(" " | "\t" | "\r") -> advance(state) |> skip_whitespace
    _ -> state
  }
}

fn handle_newline(state: LexerState) -> LexerState {
  let state = advance(state)
  LexerState(..state, line: state.line + 1, column: 1)
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
  let start_pos = Position(state.pos, state.line, state.column)
  let state = advance(state) // Skip opening quote
  let #(content, state) = read_string_content(state, "")

  let end_pos = Position(state.pos, state.line, state.column)
  let token = Token(
    kind: "String",
    value: content,
    start: start_pos,
    end: end_pos,
  )

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
  let start_pos = Position(state.pos, state.line, state.column)
  let #(digits, state) = read_digits(state, "")

  // Check for decimal point
  let #(digits, state) = case peek_char(state) {
    Some(".") -> {
      case peek_next_char(state) {
        Some(d) if is_digit(d) -> {
          let state = advance(state) // Skip "."
          let #(frac_digits, state) = read_digits(state, digits <> ".")
          #(frac_digits, state)
        }
        _ -> #(digits, state)
      }
    }
    _ -> #(digits, state)
  }

  let end_pos = Position(state.pos, state.line, state.column)
  let token = Token(
    kind: "Number",
    value: digits,
    start: start_pos,
    end: end_pos,
  )

  LexerState(..state, tokens: [token, ..state.tokens])
}

fn read_digits(state: LexerState, acc: String) -> #(String, LexerState) {
  case peek_char(state) {
    Some(d) if is_digit(d) -> read_digits(advance(state), acc <> d)
    _ -> #(acc, state)
  }
}

fn is_digit(char: String) -> Bool {
  case char {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

fn tokenize_ident(state: LexerState) -> LexerState {
  let start_pos = Position(state.pos, state.line, state.column)
  let #(chars, state) = read_ident_chars(state, "")
  let value = string.concat(chars)

  let kind = case value {
    "let" | "in" | "fn" | "match" | "with" | "case" | "if" | "then" | "else" |
    "true" | "false" | "Type" | "I32" | "I64" | "U32" | "U64" | "F32" | "F64" |
    "comptime" | "pub" | "import" | "type" | "opaque" -> "Keyword"
    _ -> "Ident"
  }

  let end_pos = Position(state.pos, state.line, state.column)
  let token = Token(kind: kind, value: value, start: start_pos, end: end_pos)

  LexerState(..state, tokens: [token, ..state.tokens])
}

fn read_ident_chars(state: LexerState, acc: List(String)) -> #(List(String), LexerState) {
  case peek_char(state) {
    Some(c) if is_ident_char(c) -> read_ident_chars(advance(state), [c, ..acc])
    _ -> #(list.reverse(acc), state)
  }
}

fn is_ident_char(char: String) -> Bool {
  case char {
    "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" |
    "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" |
    "y" | "z" | "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" |
    "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" |
    "W" | "X" | "Y" | "Z" | "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" |
    "8" | "9" | "_" | "λ" -> True
    _ -> False
  }
}

fn tokenize_lambda(state: LexerState) -> LexerState {
  let start_pos = Position(state.pos, state.line, state.column)
  let state = advance(state)
  let end_pos = Position(state.pos, state.line, state.column)
  let token = Token(kind: "Lambda", value: "λ", start: start_pos, end: end_pos)
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn tokenize_operator(state: LexerState) -> LexerState {
  case peek_char(state) {
    Some(char) -> {
      let start_pos = Position(state.pos, state.line, state.column)
      let state = advance(state)
      let end_pos = Position(state.pos, state.line, state.column)

      let kind = case char {
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
        "+" -> "Operator"
        "-" -> "Operator"
        "*" -> "Operator"
        "/" -> "Operator"
        "%" -> "Operator"
        "!" -> "Operator"
        "?" -> "Question"
        "|" -> "Pipe"
        ">" -> "Operator"
        "<" -> "Operator"
        "&" -> "Operator"
        "^" -> "Operator"
        "~" -> "Operator"
        "@" -> "At"
        "\\" -> "Backslash"
        "→" | "->" -> "Arrow"
        "=>" -> "FatArrow"
        _ -> "Operator"
      }

      let token = Token(kind: kind, value: char, start: start_pos, end: end_pos)
      LexerState(..state, tokens: [token, ..state.tokens])
    }
    None -> state
  }
}

// ============================================================================
// HELPERS
// ============================================================================

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
    Some("\n") -> LexerState(..state, pos: state.pos + 1, line: state.line + 1, column: 1)
    Some(_) -> LexerState(..state, pos: state.pos + 1, column: state.column + 1)
    None -> state
  }
}
