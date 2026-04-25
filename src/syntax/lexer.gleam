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
import gleam/option.{type Option, Some, None}
import gleam/string
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

fn tokenize_loop(state: State) -> State {
  case peek(state) {
    #(_, _) -> {
      let char = peek_char(state)
      case char {
        "" -> eof(state)
        " " | "\t" | "\r" -> skip_whitespace(state) |> tokenize_loop
        "\n" -> handle_newline(state) |> tokenize_loop
        "/" -> {
          case peek_next(state) {
            Some("/") -> skip_line_comment(state) |> tokenize_loop
            Some("*") -> skip_block_comment(state) |> tokenize_loop
            _ -> tokenize_op(state)
          }
        }
        "\"" -> tokenize_string(state) |> tokenize_loop
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
          tokenize_number(state) |> tokenize_loop
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
        | "Z" -> tokenize_name(state) |> tokenize_loop
        "_" -> tokenize_op(state)
        "λ" -> tokenize_lambda(state)
        _ -> tokenize_op(state)
      }
    }
  }
}

/// Peek at the current character position.
/// Returns the character at the current position and the updated span.
fn peek(state: State) -> #(String, State) {
  case state.pos < string.length(state.source) {
    True -> #(string.slice(state.source, state.pos, 1), state)
    False -> #("", state)
  }
}

/// Get the character at the current position.
fn peek_char(state: State) -> String {
  case state.pos < string.length(state.source) {
    True -> string.slice(state.source, state.pos, 1)
    False -> ""
  }
}

/// Get the next character (one position ahead).
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
  case peek(state) {
    #(" ", _) -> advance(state) |> skip_whitespace
    #("\t", _) -> advance(state) |> skip_whitespace
    #("\r", _) -> advance(state) |> skip_whitespace
    _ -> state
  }
}

fn handle_newline(state: State) -> State {
  advance(state)
}

fn skip_line_comment(state: State) -> State {
  case peek(state) {
    #("\n", _) | #("", _) -> state
    _ -> advance(state) |> skip_line_comment
  }
}

fn skip_block_comment(state: State) -> State {
  case peek(state) {
    #("", _) -> state
    #("*", _) -> {
      case peek_next(state) {
        Some("/") -> advance(state) |> advance
        _ -> advance(state) |> skip_block_comment
      }
    }
    #("\n", _) -> {
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
  case peek(state) {
    #("", _) -> #(acc, state)
    #("\"", _) -> #(acc, state)
    #("\\", _) -> {
      let state = advance(state)
      case peek(state) {
        #("n", _) -> read_string_content(advance(state), acc <> "\n")
        #("t", _) -> read_string_content(advance(state), acc <> "\t")
        #("\"", _) -> read_string_content(advance(state), acc <> "\"")
        #("\\", _) -> read_string_content(advance(state), acc <> "\\")
        _ -> read_string_content(state, acc)
      }
    }
    #(c, _) -> read_string_content(advance(state), acc <> c)
  }
}

/// Tokenize a number literal (integer or float).
fn tokenize_number(state: State) -> State {
  let start_line = state.line
  let start_col = state.col
  let #(digits, state) = read_digits(state, "")

  // Check for decimal point followed by digits (float literal)
  case peek(state) {
    #(".", _) -> {
      case peek_next(state) {
        Some("0") | Some("1") | Some("2") | Some("3") | Some("4")
        | Some("5") | Some("6") | Some("7") | Some("8") | Some("9") -> {
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
        _ -> {
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
  case peek(state) {
    #("0", _) -> read_digits(advance(state), acc <> "0")
    #("1", _) -> read_digits(advance(state), acc <> "1")
    #("2", _) -> read_digits(advance(state), acc <> "2")
    #("3", _) -> read_digits(advance(state), acc <> "3")
    #("4", _) -> read_digits(advance(state), acc <> "4")
    #("5", _) -> read_digits(advance(state), acc <> "5")
    #("6", _) -> read_digits(advance(state), acc <> "6")
    #("7", _) -> read_digits(advance(state), acc <> "7")
    #("8", _) -> read_digits(advance(state), acc <> "8")
    #("9", _) -> read_digits(advance(state), acc <> "9")
    _ -> #(acc, state)
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
  case peek(state) {
    #("a", _) -> read_ident_chars(advance(state), ["a", ..acc])
    #("b", _) -> read_ident_chars(advance(state), ["b", ..acc])
    #("c", _) -> read_ident_chars(advance(state), ["c", ..acc])
    #("d", _) -> read_ident_chars(advance(state), ["d", ..acc])
    #("e", _) -> read_ident_chars(advance(state), ["e", ..acc])
    #("f", _) -> read_ident_chars(advance(state), ["f", ..acc])
    #("g", _) -> read_ident_chars(advance(state), ["g", ..acc])
    #("h", _) -> read_ident_chars(advance(state), ["h", ..acc])
    #("i", _) -> read_ident_chars(advance(state), ["i", ..acc])
    #("j", _) -> read_ident_chars(advance(state), ["j", ..acc])
    #("k", _) -> read_ident_chars(advance(state), ["k", ..acc])
    #("l", _) -> read_ident_chars(advance(state), ["l", ..acc])
    #("m", _) -> read_ident_chars(advance(state), ["m", ..acc])
    #("n", _) -> read_ident_chars(advance(state), ["n", ..acc])
    #("o", _) -> read_ident_chars(advance(state), ["o", ..acc])
    #("p", _) -> read_ident_chars(advance(state), ["p", ..acc])
    #("q", _) -> read_ident_chars(advance(state), ["q", ..acc])
    #("r", _) -> read_ident_chars(advance(state), ["r", ..acc])
    #("s", _) -> read_ident_chars(advance(state), ["s", ..acc])
    #("t", _) -> read_ident_chars(advance(state), ["t", ..acc])
    #("u", _) -> read_ident_chars(advance(state), ["u", ..acc])
    #("v", _) -> read_ident_chars(advance(state), ["v", ..acc])
    #("w", _) -> read_ident_chars(advance(state), ["w", ..acc])
    #("x", _) -> read_ident_chars(advance(state), ["x", ..acc])
    #("y", _) -> read_ident_chars(advance(state), ["y", ..acc])
    #("z", _) -> read_ident_chars(advance(state), ["z", ..acc])
    #("A", _) -> read_ident_chars(advance(state), ["A", ..acc])
    #("B", _) -> read_ident_chars(advance(state), ["B", ..acc])
    #("C", _) -> read_ident_chars(advance(state), ["C", ..acc])
    #("D", _) -> read_ident_chars(advance(state), ["D", ..acc])
    #("E", _) -> read_ident_chars(advance(state), ["E", ..acc])
    #("F", _) -> read_ident_chars(advance(state), ["F", ..acc])
    #("G", _) -> read_ident_chars(advance(state), ["G", ..acc])
    #("H", _) -> read_ident_chars(advance(state), ["H", ..acc])
    #("I", _) -> read_ident_chars(advance(state), ["I", ..acc])
    #("J", _) -> read_ident_chars(advance(state), ["J", ..acc])
    #("K", _) -> read_ident_chars(advance(state), ["K", ..acc])
    #("L", _) -> read_ident_chars(advance(state), ["L", ..acc])
    #("M", _) -> read_ident_chars(advance(state), ["M", ..acc])
    #("N", _) -> read_ident_chars(advance(state), ["N", ..acc])
    #("O", _) -> read_ident_chars(advance(state), ["O", ..acc])
    #("P", _) -> read_ident_chars(advance(state), ["P", ..acc])
    #("Q", _) -> read_ident_chars(advance(state), ["Q", ..acc])
    #("R", _) -> read_ident_chars(advance(state), ["R", ..acc])
    #("S", _) -> read_ident_chars(advance(state), ["S", ..acc])
    #("T", _) -> read_ident_chars(advance(state), ["T", ..acc])
    #("U", _) -> read_ident_chars(advance(state), ["U", ..acc])
    #("V", _) -> read_ident_chars(advance(state), ["V", ..acc])
    #("W", _) -> read_ident_chars(advance(state), ["W", ..acc])
    #("X", _) -> read_ident_chars(advance(state), ["X", ..acc])
    #("Y", _) -> read_ident_chars(advance(state), ["Y", ..acc])
    #("Z", _) -> read_ident_chars(advance(state), ["Z", ..acc])
    #("0", _) -> read_ident_chars(advance(state), ["0", ..acc])
    #("1", _) -> read_ident_chars(advance(state), ["1", ..acc])
    #("2", _) -> read_ident_chars(advance(state), ["2", ..acc])
    #("3", _) -> read_ident_chars(advance(state), ["3", ..acc])
    #("4", _) -> read_ident_chars(advance(state), ["4", ..acc])
    #("5", _) -> read_ident_chars(advance(state), ["5", ..acc])
    #("6", _) -> read_ident_chars(advance(state), ["6", ..acc])
    #("7", _) -> read_ident_chars(advance(state), ["7", ..acc])
    #("8", _) -> read_ident_chars(advance(state), ["8", ..acc])
    #("9", _) -> read_ident_chars(advance(state), ["9", ..acc])
    #("_", _) -> read_ident_chars(advance(state), ["_", ..acc])
    _ -> #(list.reverse(acc), state)
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
fn tokenize_op(state: State) -> State {
  case peek_char(state) {
    "" -> state
    char -> {
      let start_line = state.line
      let start_col = state.col
      let span = Span(state.filename, start_line, start_col, state.line, state.col)

      // Multi-character operators (check longest first)
      case char {
        "/" -> {
          // Already handled at the top level for comments
          let state = advance(state)
          let token = Token(kind: "Op", value: "/", span: span)
          State(..state, tokens: [token, ..state.tokens])
        }
        "=" -> {
          case peek_next(state) {
            Some("=") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "==", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Punct", value: "=", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "!" -> {
          case peek_next(state) {
            Some("=") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "!=", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Op", value: "!", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "-" -> {
          case peek_next(state) {
            Some(">") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "->", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Op", value: "-", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "<" -> {
          case peek_next(state) {
            Some("-") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "<-", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            Some("=") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "<=", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Op", value: "<", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        ">" -> {
          case peek_next(state) {
            Some("=") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: ">=", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Op", value: ">", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "|" -> {
          case peek_next(state) {
            Some("|") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "||", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Punct", value: "|", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "&" -> {
          case peek_next(state) {
            Some("&") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "&&", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Op", value: "&", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "." -> {
          case peek_next(state) {
            Some(".") -> {
              let state = advance(state) |> advance
              let span = Span(state.filename, start_line, start_col, state.line, state.col)
              let token = Token(kind: "Op", value: "..", span: span)
              State(..state, tokens: [token, ..state.tokens])
            }
            _ -> {
              let token = Token(kind: "Punct", value: ".", span: span)
              State(..advance(state), tokens: [token, ..state.tokens])
            }
          }
        }
        "(" -> {
          let token = Token(kind: "Punct", value: "(", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        ")" -> {
          let token = Token(kind: "Punct", value: ")", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        "{" -> {
          let token = Token(kind: "Punct", value: "{", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        "}" -> {
          let token = Token(kind: "Punct", value: "}", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        "[" -> {
          let token = Token(kind: "Punct", value: "[", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        "]" -> {
          let token = Token(kind: "Punct", value: "]", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        "," -> {
          let token = Token(kind: "Punct", value: ",", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        ";" -> {
          let token = Token(kind: "Punct", value: ";", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        ":" -> {
          let token = Token(kind: "Punct", value: ":", span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
        _ -> {
          let token = Token(kind: "Op", value: char, span: span)
          State(..advance(state), tokens: [token, ..state.tokens])
        }
      }
    }
  }
}

fn eof(state: State) -> State {
  let token = Token(
    kind: "Eof",
    value: "",
    span: Span(state.filename, state.line, state.col, state.line, state.col),
  )
  State(..state, tokens: [token, ..state.tokens])
}
