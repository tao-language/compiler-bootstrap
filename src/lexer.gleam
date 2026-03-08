// ============================================================================
// LEXER - Tokenizer with Comment and Indentation Support
// ============================================================================

/// A lexer that converts source code to tokens with:
/// - Configurable token patterns
/// - Built-in comment handling (single-line and multi-line)
/// - Indentation tracking for Python-style languages
/// - Source location tracking
///
/// # Example
///
/// ```gleam
/// import lexer
///
/// // Create lexer with default config
/// let config = lexer.default_config()
///
/// // Tokenize source
/// let tokens = lexer.tokenize(config, "main.gleam", source)
/// ```
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import parser.{
  type Location, type Position, type Token, Location as LocationVal,
  Token as TokenVal,
}

// ============================================================================
// TYPES
// ============================================================================

/// Lexer configuration
pub type Config {
  Config(
    /// Keywords that should be recognized as such
    keywords: List(String),
    /// Single-line comment prefix (e.g., "//")
    line_comment: Option(String),
    /// Multi-line comment start (e.g., "/*")
    block_comment_start: Option(String),
    /// Multi-line comment end (e.g., "*/")
    block_comment_end: Option(String),
    /// Whether to track indentation
    indent_sensitive: Bool,
    /// Indent unit (number of spaces per level)
    indent_unit: Int,
    /// Whether to convert tabs to spaces
    tabs_to_spaces: Bool,
  )
}

/// Lexer state
type LexerState {
  LexerState(
    source: String,
    filename: String,
    pos: Position,
    offset: Int,
    tokens: List(Token),
    indent_stack: List(Int),
    pending_newlines: Int,
  )
}

// ============================================================================
// CONFIGURATION
// ============================================================================

/// Default configuration (C-style)
pub fn default_config() -> Config {
  Config(
    keywords: [],
    line_comment: Some("//"),
    block_comment_start: Some("/*"),
    block_comment_end: Some("*/"),
    indent_sensitive: False,
    indent_unit: 2,
    tabs_to_spaces: True,
  )
}

/// Python-style configuration
pub fn python_config() -> Config {
  Config(
    keywords: [
      "def",
      "class",
      "if",
      "elif",
      "else",
      "for",
      "while",
      "return",
      "import",
      "from",
      "as",
      "with",
      "try",
      "except",
      "finally",
      "raise",
      "pass",
      "break",
      "continue",
      "and",
      "or",
      "not",
      "in",
      "is",
      "True",
      "False",
      "None",
    ],
    line_comment: Some("#"),
    block_comment_start: None,
    block_comment_end: None,
    indent_sensitive: True,
    indent_unit: 4,
    tabs_to_spaces: True,
  )
}

/// Gleam-style configuration
pub fn gleam_config() -> Config {
  Config(
    keywords: [
      "pub",
      "fn",
      "let",
      "case",
      "of",
      "if",
      "else",
      "use",
      "type",
      "opaque",
      "import",
      "as",
      "const",
      "todo",
      "panic",
      "True",
      "False",
    ],
    line_comment: Some("//"),
    block_comment_start: Some("/*"),
    block_comment_end: Some("*/"),
    indent_sensitive: False,
    indent_unit: 2,
    tabs_to_spaces: True,
  )
}

/// Add keywords
pub fn with_keywords(config: Config, kws: List(String)) -> Config {
  Config(..config, keywords: kws)
}

/// Enable indentation sensitivity
pub fn with_indent_sensitivity(config: Config, unit: Int) -> Config {
  Config(..config, indent_sensitive: True, indent_unit: unit)
}

/// Set comment style
pub fn with_comments(
  config: Config,
  line_comment: Option(String),
  block_start: Option(String),
  block_end: Option(String),
) -> Config {
  Config(
    ..config,
    line_comment: line_comment,
    block_comment_start: block_start,
    block_comment_end: block_end,
  )
}

// ============================================================================
// TOKENIZATION
// ============================================================================

/// Tokenize source code
pub fn tokenize(config: Config, filename: String, source: String) -> List(Token) {
  let initial_state =
    LexerState(
      source: source,
      filename: filename,
      pos: parser.Position(1, 1, 0),
      offset: 0,
      tokens: [],
      indent_stack: [0],
      pending_newlines: 0,
    )

  let final_state = lex_loop(config, initial_state)

  // Add EOF token
  let eof_token =
    TokenVal(
      kind: "EOF",
      value: "",
      location: make_location(final_state.pos, final_state.pos),
      indent: get_indent(final_state.indent_stack),
    )

  // Close any open indentation blocks
  let tokens_with_dedents =
    close_indents(final_state.tokens, final_state.indent_stack, final_state.pos)

  list.reverse([eof_token, ..tokens_with_dedents])
}

fn lex_loop(config: Config, state: LexerState) -> LexerState {
  case string.is_empty(state.source) {
    True -> state
    False -> {
      case next_token(config, state) {
        Some(new_state) -> lex_loop(config, new_state)
        None -> state
      }
    }
  }
}

fn next_token(config: Config, state: LexerState) -> Option(LexerState) {
  let source = state.source

  // Skip whitespace (but track newlines for indentation)
  case string.pop_grapheme(source) {
    Error(_) -> None
    Ok(#(char, rest)) -> {
      case char {
        " " -> {
          // Space - just advance
          Some(advance_state(state, 1))
        }
        "\t" -> {
          // Tab - convert to spaces if configured
          let spaces = config.indent_unit
          Some(advance_state(state, spaces))
        }
        "\n" -> {
          // Newline - track for indentation
          handle_newline(config, state, rest)
        }
        "\r" -> {
          // Carriage return - skip
          Some(advance_state(state, 1))
        }
        _ -> {
          // Check for comments
          case try_match_comment(config, source, state) {
            Some(new_state) -> Some(new_state)
            None -> {
              // Check for indentation change (if enabled)
              case config.indent_sensitive && state.pending_newlines > 0 {
                True -> handle_indent(config, state, source)
                False -> {
                  // Regular token
                  tokenize_char(config, char, rest, state)
                }
              }
            }
          }
        }
      }
    }
  }
}

fn handle_newline(
  config: Config,
  state: LexerState,
  rest: String,
) -> Option(LexerState) {
  let new_pending = state.pending_newlines + 1
  Some(LexerState(
    source: rest,
    filename: state.filename,
    pos: parser.Position(state.pos.row + 1, 1, state.offset + 1),
    offset: state.offset + 1,
    tokens: state.tokens,
    indent_stack: state.indent_stack,
    pending_newlines: new_pending,
  ))
}

fn handle_indent(
  config: Config,
  state: LexerState,
  source: String,
) -> Option(LexerState) {
  // Count leading spaces
  let indent = count_indent(source, config.indent_unit)
  let current_indent = get_indent(state.indent_stack)

  let new_state =
    LexerState(
      source: string.drop_start(source, indent),
      filename: state.filename,
      pos: parser.Position(state.pos.row, 1 + indent, state.offset + indent),
      offset: state.offset + indent,
      tokens: state.tokens,
      indent_stack: state.indent_stack,
      pending_newlines: 0,
    )

  case indent > current_indent {
    True -> {
      // Indent - push to stack and add Indent token
      let indent_token =
        TokenVal(
          kind: "Indent",
          value: "",
          location: make_location(state.pos, state.pos),
          indent: indent,
        )
      Some(
        LexerState(
          ..new_state,
          tokens: [indent_token, ..state.tokens],
          indent_stack: [indent, ..state.indent_stack],
        ),
      )
    }
    False if indent < current_indent -> {
      // Dedent - pop from stack and add Dedent token(s)
      add_dedents(config, new_state, indent)
    }
    False -> {
      // Same indent - just continue
      Some(new_state)
    }
  }
}

fn count_indent(source: String, unit: Int) -> Int {
  count_indent_loop(source, 0, unit)
}

fn count_indent_loop(source: String, count: Int, unit: Int) -> Int {
  case string.pop_grapheme(source) {
    Error(_) -> count
    Ok(#(" ", rest)) -> count_indent_loop(rest, count + 1, unit)
    Ok(#("\t", rest)) -> count_indent_loop(rest, count + unit, unit)
    Ok(_) -> count
  }
}

fn add_dedents(
  config: Config,
  state: LexerState,
  target_indent: Int,
) -> Option(LexerState) {
  case state.indent_stack {
    [] -> Some(state)
    [current, ..rest] if current > target_indent -> {
      let dedent_token =
        TokenVal(
          kind: "Dedent",
          value: "",
          location: make_location(state.pos, state.pos),
          indent: target_indent,
        )
      add_dedents(
        config,
        LexerState(
          ..state,
          tokens: [dedent_token, ..state.tokens],
          indent_stack: rest,
        ),
        target_indent,
      )
    }
    _ -> Some(state)
  }
}

fn close_indents(
  tokens: List(Token),
  indent_stack: List(Int),
  pos: Position,
) -> List(Token) {
  case indent_stack {
    [] | [0] -> tokens
    [_, ..rest] -> {
      let dedent_token =
        TokenVal(
          kind: "Dedent",
          value: "",
          location: make_location(pos, pos),
          indent: 0,
        )
      close_indents([dedent_token, ..tokens], rest, pos)
    }
  }
}

fn try_match_comment(
  config: Config,
  source: String,
  state: LexerState,
) -> Option(LexerState) {
  // Check for line comment
  case config.line_comment {
    Some(prefix) ->
      case string.starts_with(source, prefix) {
        True -> Some(skip_line_comment(source, prefix, state))
        False -> try_match_block_comment(config, source, state)
      }
    None -> try_match_block_comment(config, source, state)
  }
}

fn try_match_block_comment(
  config: Config,
  source: String,
  state: LexerState,
) -> Option(LexerState) {
  case config.block_comment_start, config.block_comment_end {
    Some(start), Some(end) ->
      case string.starts_with(source, start) {
        True -> Some(skip_block_comment(source, start, end, state))
        False -> None
      }
    _, _ -> None
  }
}

fn skip_line_comment(
  source: String,
  prefix: String,
  state: LexerState,
) -> LexerState {
  let rest = string.drop_start(source, string.length(prefix))
  // Find newline position manually
  let newline_pos = find_newline_pos(rest, 0)
  case newline_pos {
    Some(idx) -> {
      let skipped = string.length(prefix) + idx
      advance_state(state, skipped)
    }
    None -> {
      // Comment extends to end of file
      advance_state(state, string.length(source))
    }
  }
}

fn find_newline_pos(text: String, pos: Int) -> Option(Int) {
  case string.pop_grapheme(text) {
    Error(_) -> None
    Ok(#("\n", _)) -> Some(pos)
    Ok(#(_, rest)) -> find_newline_pos(rest, pos + 1)
  }
}

fn skip_block_comment(
  source: String,
  start: String,
  end: String,
  state: LexerState,
) -> LexerState {
  let after_start = string.drop_start(source, string.length(start))
  // Find end position manually
  let end_pos = find_string_pos(after_start, end, 0)
  case end_pos {
    Some(idx) -> {
      let skipped = string.length(start) + idx + string.length(end)
      advance_state_with_newlines(
        state,
        string.slice(after_start, 0, idx),
        skipped,
      )
    }
    None -> {
      // Unterminated comment - skip to end
      advance_state_with_newlines(state, after_start, string.length(source))
    }
  }
}

fn find_string_pos(text: String, target: String, pos: Int) -> Option(Int) {
  case string.starts_with(text, target) {
    True -> Some(pos)
    False -> {
      case string.pop_grapheme(text) {
        Error(_) -> None
        Ok(#(_, rest)) -> find_string_pos(rest, target, pos + 1)
      }
    }
  }
}

fn advance_state_with_newlines(
  state: LexerState,
  text: String,
  skip: Int,
) -> LexerState {
  let newlines = count_newlines(text)
  let new_col = case string.pop_grapheme(string.reverse(text)) {
    Ok(#(last, _)) -> state.pos.col + string.length(last)
    Error(_) -> state.pos.col
  }
  LexerState(
    source: string.drop_start(state.source, skip),
    filename: state.filename,
    pos: parser.Position(state.pos.row + newlines, new_col, state.offset + skip),
    offset: state.offset + skip,
    tokens: state.tokens,
    indent_stack: state.indent_stack,
    pending_newlines: state.pending_newlines + newlines,
  )
}

fn count_newlines(text: String) -> Int {
  count_newlines_loop(text, 0)
}

fn count_newlines_loop(text: String, count: Int) -> Int {
  case string.pop_grapheme(text) {
    Error(_) -> count
    Ok(#("\n", rest)) -> count_newlines_loop(rest, count + 1)
    Ok(#(_, rest)) -> count_newlines_loop(rest, count)
  }
}

fn tokenize_char(
  config: Config,
  char: String,
  rest: String,
  state: LexerState,
) -> Option(LexerState) {
  case char {
    // Identifiers and keywords
    _ -> {
      case is_ident_start(char) {
        True -> {
          let ident = read_ident(state.source)
          let kind = case list.contains(config.keywords, ident) {
            True -> "Keyword"
            False -> "Ident"
          }
          let token =
            TokenVal(
              kind: kind,
              value: ident,
              location: make_location(state.pos, advance_pos(state.pos, ident)),
              indent: get_indent(state.indent_stack),
            )
          let skip = string.length(ident)
          Some(LexerState(
            source: string.drop_start(state.source, skip),
            filename: state.filename,
            pos: advance_pos(state.pos, ident),
            offset: state.offset + skip,
            tokens: [token, ..state.tokens],
            indent_stack: state.indent_stack,
            pending_newlines: state.pending_newlines,
          ))
        }
        False -> tokenize_non_ident(config, char, rest, state)
      }
    }
  }
}

fn tokenize_non_ident(
  config: Config,
  char: String,
  rest: String,
  state: LexerState,
) -> Option(LexerState) {
  case is_digit(char) {
    // Numbers
    True -> {
      let num = read_number(state.source)
      let token =
        TokenVal(
          kind: "Number",
          value: num,
          location: make_location(state.pos, advance_pos(state.pos, num)),
          indent: get_indent(state.indent_stack),
        )
      let skip = string.length(num)
      Some(LexerState(
        source: string.drop_start(state.source, skip),
        filename: state.filename,
        pos: advance_pos(state.pos, num),
        offset: state.offset + skip,
        tokens: [token, ..state.tokens],
        indent_stack: state.indent_stack,
        pending_newlines: state.pending_newlines,
      ))
    }
    False -> tokenize_non_digit(config, char, rest, state)
  }
}

fn tokenize_non_digit(
  config: Config,
  char: String,
  rest: String,
  state: LexerState,
) -> Option(LexerState) {
  case char {
    // Strings
    "\"" -> {
      case read_string(state.source) {
        Ok(#(str, skip)) -> {
          let token =
            TokenVal(
              kind: "String",
              value: str,
              location: make_location(state.pos, advance_pos(state.pos, str)),
              indent: get_indent(state.indent_stack),
            )
          Some(LexerState(
            source: string.drop_start(state.source, skip),
            filename: state.filename,
            pos: advance_pos(state.pos, str),
            offset: state.offset + skip,
            tokens: [token, ..state.tokens],
            indent_stack: state.indent_stack,
            pending_newlines: state.pending_newlines,
          ))
        }
        Error(_) -> Some(advance_state(state, 1))
      }
    }
    // Parentheses
    "(" -> {
      let token =
        TokenVal(
          kind: "LParen",
          value: "(",
          location: make_location(state.pos, advance_pos(state.pos, "(")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    ")" -> {
      let token =
        TokenVal(
          kind: "RParen",
          value: ")",
          location: make_location(state.pos, advance_pos(state.pos, ")")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Brackets
    "[" -> {
      let token =
        TokenVal(
          kind: "LBracket",
          value: "[",
          location: make_location(state.pos, advance_pos(state.pos, "[")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    "]" -> {
      let token =
        TokenVal(
          kind: "RBracket",
          value: "]",
          location: make_location(state.pos, advance_pos(state.pos, "]")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Braces
    "{" -> {
      let token =
        TokenVal(
          kind: "LBrace",
          value: "{",
          location: make_location(state.pos, advance_pos(state.pos, "{")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    "}" -> {
      let token =
        TokenVal(
          kind: "RBrace",
          value: "}",
          location: make_location(state.pos, advance_pos(state.pos, "}")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Comma
    "," -> {
      let token =
        TokenVal(
          kind: "Comma",
          value: ",",
          location: make_location(state.pos, advance_pos(state.pos, ",")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Semicolon
    ";" -> {
      let token =
        TokenVal(
          kind: "Semicolon",
          value: ";",
          location: make_location(state.pos, advance_pos(state.pos, ";")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Colon
    ":" -> {
      let token =
        TokenVal(
          kind: "Colon",
          value: ":",
          location: make_location(state.pos, advance_pos(state.pos, ":")),
          indent: get_indent(state.indent_stack),
        )
      Some(advance_state(state, 1) |> add_token(token))
    }
    // Other operators
    _ -> {
      let op = read_operator(state.source)
      let token =
        TokenVal(
          kind: "Operator",
          value: op,
          location: make_location(state.pos, advance_pos(state.pos, op)),
          indent: get_indent(state.indent_stack),
        )
      let skip = string.length(op)
      Some(LexerState(
        source: string.drop_start(state.source, skip),
        filename: state.filename,
        pos: advance_pos(state.pos, op),
        offset: state.offset + skip,
        tokens: [token, ..state.tokens],
        indent_stack: state.indent_stack,
        pending_newlines: state.pending_newlines,
      ))
    }
  }
}

fn add_token(state: LexerState, token: Token) -> LexerState {
  LexerState(..state, tokens: [token, ..state.tokens])
}

fn advance_state(state: LexerState, skip: Int) -> LexerState {
  let text = string.slice(state.source, 0, skip)
  let newlines = count_newlines(text)
  let last_line = last_line_of(text)
  let new_col = case newlines > 0 {
    True -> string.length(last_line)
    False -> state.pos.col + skip
  }
  LexerState(
    source: string.drop_start(state.source, skip),
    filename: state.filename,
    pos: parser.Position(state.pos.row + newlines, new_col, state.offset + skip),
    offset: state.offset + skip,
    tokens: state.tokens,
    indent_stack: state.indent_stack,
    pending_newlines: state.pending_newlines + newlines,
  )
}

fn last_line_of(text: String) -> String {
  case string.split(text, "\n") {
    [] -> ""
    lines -> list.last(lines) |> result.unwrap("")
  }
}

fn make_location(start: parser.Position, end: parser.Position) -> Location {
  LocationVal(filename: "unknown", start: start, end: end)
}

fn advance_pos(pos: parser.Position, text: String) -> parser.Position {
  let newlines = count_newlines(text)
  let last_line = last_line_of(text)
  parser.Position(
    row: pos.row + newlines,
    col: case newlines > 0 {
      True -> string.length(last_line) + 1
      False -> pos.col + string.length(text)
    },
    offset: pos.offset + string.length(text),
  )
}

// ============================================================================
// TOKEN READERS
// ============================================================================

fn read_ident(source: String) -> String {
  read_ident_loop(source, "")
}

fn read_ident_loop(source: String, acc: String) -> String {
  case string.pop_grapheme(source) {
    Error(_) -> acc
    Ok(#(c, rest)) -> {
      case is_ident_continue(c) {
        True -> read_ident_loop(rest, acc <> c)
        False -> acc
      }
    }
  }
}

fn is_ident_start(c: String) -> Bool {
  case c {
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
    | "_" -> True
    _ -> False
  }
}

fn is_ident_continue(c: String) -> Bool {
  is_ident_start(c) || is_digit(c)
}

fn read_number(source: String) -> String {
  read_number_loop(source, "", False)
}

fn read_number_loop(source: String, acc: String, has_dot: Bool) -> String {
  case string.pop_grapheme(source) {
    Error(_) -> acc
    Ok(#(".", rest)) -> {
      case has_dot {
        False -> {
          case string.pop_grapheme(rest) {
            Ok(#(d, rest2)) -> {
              case is_digit(d) {
                True -> read_number_loop(rest2, acc <> ".", True)
                False -> acc
              }
            }
            Error(_) -> acc
          }
        }
        True -> acc
      }
    }
    Ok(#(c, rest)) -> {
      case is_digit(c) {
        True -> read_number_loop(rest, acc <> c, has_dot)
        False -> acc
      }
    }
  }
}

fn is_digit(c: String) -> Bool {
  case c {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

fn read_string(source: String) -> Result(#(String, Int), Nil) {
  case string.pop_grapheme(source) {
    Error(_) -> Error(Nil)
    Ok(#("\"", _)) -> read_string_loop(string.drop_start(source, 1), "", 1)
    Ok(_) -> Error(Nil)
  }
}

fn read_string_loop(
  source: String,
  acc: String,
  len: Int,
) -> Result(#(String, Int), Nil) {
  case string.pop_grapheme(source) {
    Error(_) -> Error(Nil)
    Ok(#("\\", rest)) -> {
      case string.pop_grapheme(rest) {
        Ok(#(c, rest2)) -> read_string_loop(rest2, acc <> "\\", len + 2)
        Error(_) -> Error(Nil)
      }
    }
    Ok(#("\"", _)) -> Ok(#(acc, len + 1))
    Ok(#(c, rest)) -> read_string_loop(rest, acc <> c, len + 1)
  }
}

fn read_operator(source: String) -> String {
  read_operator_loop(source, "")
}

fn read_operator_loop(source: String, acc: String) -> String {
  case string.pop_grapheme(source) {
    Error(_) -> acc
    Ok(#(c, rest)) -> {
      case is_operator_char(c) {
        True -> read_operator_loop(rest, acc <> c)
        False -> {
          case acc == "" {
            True -> c
            False -> acc
          }
        }
      }
    }
  }
}

fn get_indent(indent_stack: List(Int)) -> Int {
  list.fold(indent_stack, 0, fn(_acc, x) { x })
}

fn is_operator_char(c: String) -> Bool {
  case c {
    "+"
    | "-"
    | "*"
    | "/"
    | "%"
    | "="
    | "<"
    | ">"
    | "!"
    | "&"
    | "|"
    | "^"
    | "~"
    | "."
    | ","
    | ";"
    | ":"
    | "?"
    | "@"
    | "#"
    | "$" -> True
    _ -> False
  }
}
