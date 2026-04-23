/// Tokenizer - converts source text into a list of tokens.
/// Tokens include keywords, identifiers, operators, literals, and punctuation.
import gleam/list
import gleam/string
import gleam/option.{type Option, None, Some}

pub type Token {
  Token(kind: String, value: String, span: Span)
}

pub type Span {
  Span(file: String, line: Int, column: Int)
}

type State {
  State(source: String, file: String, pos: Int, line: Int, column: Int, tokens: List(Token))
}

pub fn tokenize(source: String, file: String) -> List(Token) {
  let state = State(source, file, 0, 1, 1, [])
  case tokenize_loop(state) {
    Ok(final) -> list.reverse(final.tokens)
    Error(_) -> []
  }
}

pub fn token_kinds(tokens: List(Token)) -> List(String) {
  list.map(tokens, fn(t) { t.kind })
}

fn tokenize_loop(state: State) -> Result(State, List(Token)) {
  case peek_char(state) {
    None -> Ok(state)
    Some(c) -> {
      case c {
        " " | "\t" | "\r" -> tokenize_loop(skip_ws(state))
        "\n" -> tokenize_loop(advance(state))
        "/" -> tokenize_loop(handle_slash(state))
        "\"" -> tokenize_loop(handle_string(state))
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> tokenize_loop(handle_number(state))
        "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" -> tokenize_loop(handle_ident(state))
        "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" | "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" -> tokenize_loop(handle_ident(state))
        "_" -> tokenize_loop(handle_underscore(state))
        "λ" -> tokenize_loop(handle_lambda(state))
        "?" -> tokenize_loop(handle_question(state))
        "\\" -> tokenize_loop(handle_backslash(state))
        _ -> tokenize_loop(handle_op(state))
      }
    }
  }
}

fn skip_ws(state: State) -> State {
  case peek_char(state) {
    Some(c) if c == " " || c == "\t" || c == "\r" -> skip_ws(advance(state))
    _ -> state
  }
}

fn handle_slash(state: State) -> State {
  case peek_next_char(state) {
    Some("/") -> {
      let state = advance(state)
      read_until_newline(state)
    }
    Some("*") -> {
      let state = advance(state)
      read_block_comment(state)
    }
    _ -> {
      // Single / is an operator
      let s = advance(state)
      let kind = tk("/")
      let span = Span(file: s.file, line: s.line, column: s.column)
      let token = Token(kind: kind, value: "/", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
  }
}

fn read_until_newline(state: State) -> State {
  case peek_char(state) {
    Some("\n") | None -> state
    Some(_) -> read_until_newline(advance(state))
  }
}

fn read_block_comment(state: State) -> State {
  case peek_char(state) {
    Some("*") -> {
      case peek_next_char(state) {
        Some("/") -> advance(state) |> advance
        _ -> read_block_comment(advance(state))
      }
    }
    Some("\n") -> {
      let state = advance(state)
      State(..state, line: state.line + 1, column: 1) |> read_block_comment
    }
    None -> state
    Some(_) -> read_block_comment(advance(state))
  }
}

fn handle_string(state: State) -> State {
  let line = state.line
  let col = state.column
  let state = advance(state)
  let #(content, state) = read_string_content(state, "")
  case peek_char(state) {
    Some("\"") -> {
      let state = advance(state)
      let span = Span(file: state.file, line: line, column: col)
      let token = Token(kind: "String", value: content, span: span)
      State(..state, tokens: [token, ..state.tokens])
    }
    _ -> state
  }
}

fn read_string_content(state: State, acc: String) -> #(String, State) {
  case peek_char(state) {
    None -> #(acc, state)
    Some("\"") -> #(acc, state)
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
    Some(c) -> read_string_content(advance(state), acc <> c)
  }
}

fn handle_number(state: State) -> State {
  let line = state.line
  let col = state.column
  let #(digits, state) = read_num_digits(state, "")
  case peek_char(state) {
    Some(".") -> {
      case peek_next_char(state) {
        Some("0") | Some("1") | Some("2") | Some("3") | Some("4") | Some("5") | Some("6") | Some("7") | Some("8") | Some("9") -> {
          let state = advance(state)
          let #(frac, state) = read_num_digits(state, "")
          let value = digits <> "." <> frac
          let span = Span(file: state.file, line: line, column: col)
          let token = Token(kind: "Float", value: value, span: span)
          State(..state, tokens: [token, ..state.tokens])
        }
        _ -> {
          let span = Span(file: state.file, line: line, column: col)
          let token = Token(kind: "Number", value: digits, span: span)
          State(..state, tokens: [token, ..state.tokens])
        }
      }
    }
    _ -> {
      let span = Span(file: state.file, line: line, column: col)
      let token = Token(kind: "Number", value: digits, span: span)
      State(..state, tokens: [token, ..state.tokens])
    }
  }
}

fn read_num_digits(state: State, acc: String) -> #(String, State) {
  case peek_char(state) {
    Some("0") -> read_num_digits(advance(state), acc <> "0")
    Some("1") -> read_num_digits(advance(state), acc <> "1")
    Some("2") -> read_num_digits(advance(state), acc <> "2")
    Some("3") -> read_num_digits(advance(state), acc <> "3")
    Some("4") -> read_num_digits(advance(state), acc <> "4")
    Some("5") -> read_num_digits(advance(state), acc <> "5")
    Some("6") -> read_num_digits(advance(state), acc <> "6")
    Some("7") -> read_num_digits(advance(state), acc <> "7")
    Some("8") -> read_num_digits(advance(state), acc <> "8")
    Some("9") -> read_num_digits(advance(state), acc <> "9")
    _ -> #(acc, state)
  }
}

fn handle_ident(state: State) -> State {
  let line = state.line
  let col = state.column
  let #(chars, state) = read_ident_chars(state, [])
  let value = string.join(chars, "")
  let kind = kw(value)
  let span = Span(file: state.file, line: line, column: col)
  let token = Token(kind: kind, value: value, span: span)
  State(..state, tokens: [token, ..state.tokens])
}

fn handle_underscore(state: State) -> State {
  let line = state.line
  let col = state.column
  let #(chars, state) = read_ident_chars(state, ["_"])
  let value = string.join(chars, "")
  let kind = kw(value)
  let span = Span(file: state.file, line: line, column: col)
  let token = Token(kind: kind, value: value, span: span)
  State(..state, tokens: [token, ..state.tokens])
}

fn handle_lambda(state: State) -> State {
  let line = state.line
  let col = state.column
  let state = advance(state)
  let span = Span(file: state.file, line: line, column: col)
  let token = Token(kind: "Lambda", value: "λ", span: span)
  State(..state, tokens: [token, ..state.tokens])
}

fn handle_question(state: State) -> State {
  let line = state.line
  let col = state.column
  let state = advance(state)
  let span = Span(file: state.file, line: line, column: col)
  let token = Token(kind: "Question", value: "?", span: span)
  State(..state, tokens: [token, ..state.tokens])
}

fn handle_backslash(state: State) -> State {
  let line = state.line
  let col = state.column
  let state = advance(state)
  let span = Span(file: state.file, line: line, column: col)
  let token = Token(kind: "Backslash", value: "\\", span: span)
  State(..state, tokens: [token, ..state.tokens])
}

fn kw(v: String) -> String {
  case v {
    "in" -> "In"
    "fn" -> "Keyword"
    "case" | "if" | "then" | "else" | "pub" | "import" | "type" | "opaque" | "match" | "let" | "mut" | "export" | "as" | "true" | "false" | "for" | "while" | "loop" | "break" | "continue" | "return" | "yield" | "and" | "or" | "not" | "where" | "using" -> "Keyword"
    _ -> "Ident"
  }
}

fn read_ident_chars(state: State, acc: List(String)) -> #(List(String), State) {
  case peek_char(state) {
    Some("0") -> read_ident_chars(advance(state), ["0", ..acc])
    Some("1") -> read_ident_chars(advance(state), ["1", ..acc])
    Some("2") -> read_ident_chars(advance(state), ["2", ..acc])
    Some("3") -> read_ident_chars(advance(state), ["3", ..acc])
    Some("4") -> read_ident_chars(advance(state), ["4", ..acc])
    Some("5") -> read_ident_chars(advance(state), ["5", ..acc])
    Some("6") -> read_ident_chars(advance(state), ["6", ..acc])
    Some("7") -> read_ident_chars(advance(state), ["7", ..acc])
    Some("8") -> read_ident_chars(advance(state), ["8", ..acc])
    Some("9") -> read_ident_chars(advance(state), ["9", ..acc])
    Some("a") -> read_ident_chars(advance(state), ["a", ..acc])
    Some("b") -> read_ident_chars(advance(state), ["b", ..acc])
    Some("c") -> read_ident_chars(advance(state), ["c", ..acc])
    Some("d") -> read_ident_chars(advance(state), ["d", ..acc])
    Some("e") -> read_ident_chars(advance(state), ["e", ..acc])
    Some("f") -> read_ident_chars(advance(state), ["f", ..acc])
    Some("g") -> read_ident_chars(advance(state), ["g", ..acc])
    Some("h") -> read_ident_chars(advance(state), ["h", ..acc])
    Some("i") -> read_ident_chars(advance(state), ["i", ..acc])
    Some("j") -> read_ident_chars(advance(state), ["j", ..acc])
    Some("k") -> read_ident_chars(advance(state), ["k", ..acc])
    Some("l") -> read_ident_chars(advance(state), ["l", ..acc])
    Some("m") -> read_ident_chars(advance(state), ["m", ..acc])
    Some("n") -> read_ident_chars(advance(state), ["n", ..acc])
    Some("o") -> read_ident_chars(advance(state), ["o", ..acc])
    Some("p") -> read_ident_chars(advance(state), ["p", ..acc])
    Some("q") -> read_ident_chars(advance(state), ["q", ..acc])
    Some("r") -> read_ident_chars(advance(state), ["r", ..acc])
    Some("s") -> read_ident_chars(advance(state), ["s", ..acc])
    Some("t") -> read_ident_chars(advance(state), ["t", ..acc])
    Some("u") -> read_ident_chars(advance(state), ["u", ..acc])
    Some("v") -> read_ident_chars(advance(state), ["v", ..acc])
    Some("w") -> read_ident_chars(advance(state), ["w", ..acc])
    Some("x") -> read_ident_chars(advance(state), ["x", ..acc])
    Some("y") -> read_ident_chars(advance(state), ["y", ..acc])
    Some("z") -> read_ident_chars(advance(state), ["z", ..acc])
    Some("A") -> read_ident_chars(advance(state), ["A", ..acc])
    Some("B") -> read_ident_chars(advance(state), ["B", ..acc])
    Some("C") -> read_ident_chars(advance(state), ["C", ..acc])
    Some("D") -> read_ident_chars(advance(state), ["D", ..acc])
    Some("E") -> read_ident_chars(advance(state), ["E", ..acc])
    Some("F") -> read_ident_chars(advance(state), ["F", ..acc])
    Some("G") -> read_ident_chars(advance(state), ["G", ..acc])
    Some("H") -> read_ident_chars(advance(state), ["H", ..acc])
    Some("I") -> read_ident_chars(advance(state), ["I", ..acc])
    Some("J") -> read_ident_chars(advance(state), ["J", ..acc])
    Some("K") -> read_ident_chars(advance(state), ["K", ..acc])
    Some("L") -> read_ident_chars(advance(state), ["L", ..acc])
    Some("M") -> read_ident_chars(advance(state), ["M", ..acc])
    Some("N") -> read_ident_chars(advance(state), ["N", ..acc])
    Some("O") -> read_ident_chars(advance(state), ["O", ..acc])
    Some("P") -> read_ident_chars(advance(state), ["P", ..acc])
    Some("Q") -> read_ident_chars(advance(state), ["Q", ..acc])
    Some("R") -> read_ident_chars(advance(state), ["R", ..acc])
    Some("S") -> read_ident_chars(advance(state), ["S", ..acc])
    Some("T") -> read_ident_chars(advance(state), ["T", ..acc])
    Some("U") -> read_ident_chars(advance(state), ["U", ..acc])
    Some("V") -> read_ident_chars(advance(state), ["V", ..acc])
    Some("W") -> read_ident_chars(advance(state), ["W", ..acc])
    Some("X") -> read_ident_chars(advance(state), ["X", ..acc])
    Some("Y") -> read_ident_chars(advance(state), ["Y", ..acc])
    Some("Z") -> read_ident_chars(advance(state), ["Z", ..acc])
    Some("_") -> read_ident_chars(advance(state), ["_", ..acc])
    _ -> #(list.reverse(acc), state)
  }
}

fn handle_op(state: State) -> State {
  case peek_char(state) {
    None -> state
    Some(c) -> {
      let line = state.line
      let col = state.column
      let next = peek_char_string(state)
      
      case c == "-" && next == ">" {
        True -> {
          let s = advance(state) |> advance
          let span = Span(file: s.file, line: line, column: col)
          let token = Token(kind: "Arrow", value: "->", span: span)
          State(..s, tokens: [token, ..s.tokens])
        }
        False -> handle_op_2(state, c, line, col, next)
      }
    }
  }
}

fn handle_op_2(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "<" && next == "-" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "Arrow", value: "<-", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_3(state, c, line, col, next)
  }
}

fn handle_op_3(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "=" && next == "=" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "Equal", value: "==", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_4(state, c, line, col, next)
  }
}

fn handle_op_4(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "!" && next == "=" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "NotEqual", value: "!=", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_5(state, c, line, col, next)
  }
}

fn handle_op_5(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "|" && next == "|" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "PipePipe", value: "||", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_6(state, c, line, col, next)
  }
}

fn handle_op_6(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "&" && next == "&" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "AmpersandAmpersand", value: "&&", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_7(state, c, line, col, next)
  }
}

fn handle_op_7(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "<" && next == "=" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "LessEqual", value: "<=", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_8(state, c, line, col, next)
  }
}

fn handle_op_8(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == ">" && next == "=" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "GreaterEqual", value: ">=", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_9(state, c, line, col, next)
  }
}

fn handle_op_9(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "." && next == "." {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "DotDot", value: "..", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_10(state, c, line, col, next)
  }
}

fn handle_op_10(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == ":" && next == "=" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "Assign", value: ":=", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> handle_op_11(state, c, line, col, next)
  }
}

fn handle_op_11(state: State, c: String, line: Int, col: Int, _next: String) -> State {
  let next = peek_char_string(state)
  case c == "=" && next == ">" {
    True -> {
      let s = advance(state) |> advance
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: "FatArrow", value: "=>", span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
    False -> {
      let s = advance(state)
      let kind = tk(c)
      let span = Span(file: s.file, line: line, column: col)
      let token = Token(kind: kind, value: c, span: span)
      State(..s, tokens: [token, ..s.tokens])
    }
  }
}

fn tk(c: String) -> String {
  case c {
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
    "-" | "+" | "*" | "/" | "!" | ">" | "<" | "&" | "^" | "%" -> "Operator"
    "~" -> "Tilde"
    "@" -> "At"
    "_" -> "Underscore"
    "$" -> "Dollar"
    "#" -> "Hash"
    _ -> "Operator"
  }
}

fn peek_char(state: State) -> Option(String) {
  case state.pos < string.length(state.source) {
    True -> Some(string.slice(state.source, state.pos, 1))
    False -> None
  }
}

fn peek_next_char(state: State) -> Option(String) {
  case state.pos + 1 < string.length(state.source) {
    True -> Some(string.slice(state.source, state.pos + 1, 1))
    False -> None
  }
}

fn peek_char_string(state: State) -> String {
  case peek_next_char(state) {
    Some(c) -> c
    None -> ""
  }
}

fn advance(state: State) -> State {
  case peek_char(state) {
    Some("\n") -> State(..state, pos: state.pos + 1, line: state.line + 1, column: 1)
    Some(_) -> State(..state, pos: state.pos + 1, column: state.column + 1)
    None -> state
  }
}
