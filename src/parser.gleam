// ============================================================================
// PARSER - Full Programming Language Parser Combinators
// ============================================================================

/// A comprehensive parser combinator library for defining full programming
/// languages with proper tokenization, error handling, and parse tree generation.
import gleam/int
import gleam/list
import gleam/result
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// Source position for error reporting
pub type Position {
  Position(line: Int, column: Int, offset: Int)
}

/// Token types for lexical analysis
pub type TokenType {
  TokenIdent
  TokenInt
  TokenFloat
  TokenString
  TokenKeyword(String)
  TokenOperator(String)
  TokenLParen
  TokenRParen
  TokenLBrace
  TokenRBrace
  TokenLBracket
  TokenRBracket
  TokenComma
  TokenSemi
  TokenColon
  TokenDot
  TokenArrow
  TokenEOF
}

/// A token with type, value, and position
pub type Token {
  Token(token_type: TokenType, value: String, pos: Position)
}

/// Parse error with position information
pub type ParseError {
  ParseError(message: String, pos: Position)
}

/// A parse tree node
pub type ParseTree {
  /// A token leaf
  TreeToken(Token)
  /// A named node with children
  TreeNode(name: String, children: List(ParseTree))
  /// An error node for error recovery
  TreeError(ParseError)
}

/// A parser that produces a parse tree
pub type Parser {
  Parser(run: fn(List(Token)) -> Result(#(ParseTree, List(Token)), ParseError))
}

// ============================================================================
// LEXER
// ============================================================================

/// Tokenize input string into tokens
pub fn tokenize(input: String) -> List(Token) {
  tokenize_loop(input, 0, 0, 0, [])
  |> list.reverse
}

fn tokenize_loop(
  input: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
) -> List(Token) {
  case string.pop_grapheme(input) {
    Error(_) -> [Token(TokenEOF, "", Position(line, column, offset)), ..acc]
    Ok(#(char, rest)) ->
      case char {
        // Whitespace
        " " | "\t" | "\r" -> {
          tokenize_loop(rest, offset + 1, line, column + 1, acc)
        }
        "\n" -> {
          tokenize_loop(rest, offset + 1, line + 1, 0, acc)
        }

        // Comments - skip rest of line
        "/" -> {
          case string.starts_with(rest, "/") {
            True -> skip_line_comment(rest, offset, line, column, acc)
            False -> tokenize_operator(input, offset, line, column, acc, rest)
          }
        }

        // Identifiers and keywords
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
        | "_" -> tokenize_ident(input, offset, line, column, acc, char, rest)

        // Numbers
        "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ->
          tokenize_number(input, offset, line, column, acc, char, rest)

        // Strings
        "\"" -> tokenize_string(input, offset, line, column, acc, rest)

        // Operators and punctuation
        "(" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenLParen, "(", Position(line, column, offset)),
            ..acc
          ])
        ")" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenRParen, ")", Position(line, column, offset)),
            ..acc
          ])
        "{" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenLBrace, "{", Position(line, column, offset)),
            ..acc
          ])
        "}" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenRBrace, "}", Position(line, column, offset)),
            ..acc
          ])
        "[" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenLBracket, "[", Position(line, column, offset)),
            ..acc
          ])
        "]" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenRBracket, "]", Position(line, column, offset)),
            ..acc
          ])
        "," ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenComma, ",", Position(line, column, offset)),
            ..acc
          ])
        ";" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenSemi, ";", Position(line, column, offset)),
            ..acc
          ])
        ":" ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenColon, ":", Position(line, column, offset)),
            ..acc
          ])
        "." ->
          tokenize_loop(rest, offset + 1, line, column + 1, [
            Token(TokenDot, ".", Position(line, column, offset)),
            ..acc
          ])

        // Multi-character operators
        "="
        | "+"
        | "-"
        | "*"
        | "/"
        | "<"
        | ">"
        | "!"
        | "&"
        | "|"
        | "^"
        | "%"
        | "?" -> tokenize_operator(input, offset, line, column, acc, rest)

        // Unknown character
        _ -> tokenize_loop(rest, offset + 1, line, column + 1, acc)
      }
  }
}

fn skip_line_comment(
  rest: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
) -> List(Token) {
  case string.pop_grapheme(rest) {
    Error(_) -> [Token(TokenEOF, "", Position(line, column, offset)), ..acc]
    Ok(#("\n", rest2)) -> tokenize_loop(rest2, offset + 2, line + 1, 0, acc)
    Ok(#(_, rest2)) ->
      skip_line_comment(rest2, offset + 1, line, column + 1, acc)
  }
}

fn tokenize_ident(
  input: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
  start_char: String,
  rest: String,
) -> List(Token) {
  let #(ident, remaining) = collect_while(rest, is_ident_char)
  let full_ident = start_char <> ident
  let token_type = keyword_type(full_ident)
  let pos = Position(line, column, offset)
  tokenize_loop(
    remaining,
    offset + string.length(full_ident),
    line,
    column + string.length(full_ident),
    [Token(token_type, full_ident, pos), ..acc],
  )
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
    | "_" -> True
    _ -> False
  }
}

fn keyword_type(ident: String) -> TokenType {
  case ident {
    "let"
    | "fn"
    | "if"
    | "else"
    | "match"
    | "case"
    | "type"
    | "pub"
    | "import"
    | "as"
    | "use"
    | "todo"
    | "panic" -> TokenKeyword(ident)
    _ -> TokenIdent
  }
}

fn tokenize_number(
  input: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
  start_char: String,
  rest: String,
) -> List(Token) {
  let #(num, remaining) = collect_while(rest, is_digit_char)
  let full_num = start_char <> num
  let pos = Position(line, column, offset)
  tokenize_loop(
    remaining,
    offset + string.length(full_num),
    line,
    column + string.length(full_num),
    [Token(TokenInt, full_num, pos), ..acc],
  )
}

fn is_digit_char(char: String) -> Bool {
  case char {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

fn tokenize_string(
  input: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
  rest: String,
) -> List(Token) {
  let #(str_content, remaining) = collect_until(rest, "\"")
  let pos = Position(line, column, offset)
  tokenize_loop(
    remaining,
    offset + string.length(str_content) + 2,
    line,
    column + string.length(str_content) + 2,
    [Token(TokenString, str_content, pos), ..acc],
  )
}

fn tokenize_operator(
  input: String,
  offset: Int,
  line: Int,
  column: Int,
  acc: List(Token),
  rest: String,
) -> List(Token) {
  case string.pop_grapheme(input) {
    Error(_) -> acc
    Ok(#(char, _)) -> {
      let #(op, remaining) = collect_while(rest, is_operator_char)
      let full_op = char <> op
      let pos = Position(line, column, offset)
      let token_type = case full_op {
        "->" -> TokenArrow
        _ -> TokenOperator(full_op)
      }
      tokenize_loop(
        remaining,
        offset + string.length(full_op),
        line,
        column + string.length(full_op),
        [Token(token_type, full_op, pos), ..acc],
      )
    }
  }
}

fn is_operator_char(char: String) -> Bool {
  case char {
    "="
    | "+"
    | "-"
    | "*"
    | "/"
    | "<"
    | ">"
    | "!"
    | "&"
    | "|"
    | "^"
    | "%"
    | "?"
    | "."
    | ":" -> True
    _ -> False
  }
}

fn collect_while(input: String, pred: fn(String) -> Bool) -> #(String, String) {
  collect_while_loop(input, pred, "")
}

fn collect_while_loop(
  input: String,
  pred: fn(String) -> Bool,
  acc: String,
) -> #(String, String) {
  case string.pop_grapheme(input) {
    Error(_) -> #(acc, input)
    Ok(#(char, rest)) ->
      case pred(char) {
        True -> collect_while_loop(rest, pred, acc <> char)
        False -> #(acc, input)
      }
  }
}

fn collect_until(input: String, target: String) -> #(String, String) {
  collect_until_loop(input, target, "")
}

fn collect_until_loop(
  input: String,
  target: String,
  acc: String,
) -> #(String, String) {
  case string.starts_with(input, target) {
    True -> #(acc, string.drop_start(input, string.length(target)))
    False ->
      case string.pop_grapheme(input) {
        Error(_) -> #(acc, "")
        Ok(#(char, rest)) -> collect_until_loop(rest, target, acc <> char)
      }
  }
}

// ============================================================================
// BASIC PARSERS
// ============================================================================

/// Parse a specific token type
pub fn token(t: TokenType) -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error(ParseError("Unexpected end of input", Position(0, 0, 0)))
      [tok, ..rest] if tok.token_type == t -> Ok(#(TreeToken(tok), rest))
      [tok, ..] ->
        Error(ParseError(
          "Expected "
            <> token_type_name(t)
            <> " but got "
            <> token_type_name(tok.token_type),
          tok.pos,
        ))
    }
  })
}

/// Parse a specific keyword
pub fn keyword(name: String) -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error(ParseError("Unexpected end of input", Position(0, 0, 0)))
      [tok, ..rest] if tok.token_type == TokenKeyword(name) ->
        Ok(#(TreeToken(tok), rest))
      [tok, ..] ->
        Error(ParseError(
          "Expected keyword '" <> name <> "' but got " <> token_value(tok),
          tok.pos,
        ))
    }
  })
}

/// Parse an identifier
pub fn ident() -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error(ParseError("Unexpected end of input", Position(0, 0, 0)))
      [tok, ..rest] if tok.token_type == TokenIdent ->
        Ok(#(TreeToken(tok), rest))
      [tok, ..] ->
        Error(ParseError(
          "Expected identifier but got " <> token_value(tok),
          tok.pos,
        ))
    }
  })
}

/// Parse an integer literal
pub fn int() -> Parser {
  Parser(fn(tokens) {
    case tokens {
      [] -> Error(ParseError("Unexpected end of input", Position(0, 0, 0)))
      [tok, ..rest] if tok.token_type == TokenInt -> Ok(#(TreeToken(tok), rest))
      [tok, ..] ->
        Error(ParseError(
          "Expected integer but got " <> token_value(tok),
          tok.pos,
        ))
    }
  })
}

fn token_type_name(t: TokenType) -> String {
  case t {
    TokenIdent -> "identifier"
    TokenInt -> "integer"
    TokenFloat -> "float"
    TokenString -> "string"
    TokenKeyword(_) -> "keyword"
    TokenOperator(_) -> "operator"
    TokenLParen -> "'('"
    TokenRParen -> "')'"
    TokenLBrace -> "'{'"
    TokenRBrace -> "'}'"
    TokenLBracket -> "'['"
    TokenRBracket -> "']'"
    TokenComma -> "','"
    TokenSemi -> "';'"
    TokenColon -> "':'"
    TokenDot -> "'.'"
    TokenArrow -> "'=>'"
    TokenEOF -> "end of input"
  }
}

fn token_value(tok: Token) -> String {
  tok.value
}

// ============================================================================
// COMBINATORS
// ============================================================================

/// Sequence: parse p1 then p2
pub fn seq2(p1: Parser, p2: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(r1, tokens1) <- result.try(p1.run(tokens))
    use #(r2, tokens2) <- result.try(p2.run(tokens1))
    Ok(#(TreeNode("Seq", [r1, r2]), tokens2))
  })
}

/// Sequence three parsers
pub fn seq3(p1: Parser, p2: Parser, p3: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(r1, tokens1) <- result.try(p1.run(tokens))
    use #(r2, tokens2) <- result.try(p2.run(tokens1))
    use #(r3, tokens3) <- result.try(p3.run(tokens2))
    Ok(#(TreeNode("Seq", [r1, r2, r3]), tokens3))
  })
}

/// Sequence four parsers
pub fn seq4(p1: Parser, p2: Parser, p3: Parser, p4: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(r1, tokens1) <- result.try(p1.run(tokens))
    use #(r2, tokens2) <- result.try(p2.run(tokens1))
    use #(r3, tokens3) <- result.try(p3.run(tokens2))
    use #(r4, tokens4) <- result.try(p4.run(tokens3))
    Ok(#(TreeNode("Seq", [r1, r2, r3, r4]), tokens4))
  })
}

/// Choice: try p1, if fails try p2
pub fn choice(p1: Parser, p2: Parser) -> Parser {
  Parser(fn(tokens) {
    case p1.run(tokens) {
      Ok(result) -> Ok(result)
      Error(_) -> p2.run(tokens)
    }
  })
}

/// Choice from list of parsers
pub fn choice_many(parsers: List(Parser)) -> Parser {
  Parser(fn(tokens) { choice_loop(parsers, tokens) })
}

fn choice_loop(
  parsers: List(Parser),
  tokens: List(Token),
) -> Result(#(ParseTree, List(Token)), ParseError) {
  case parsers {
    [] -> Error(ParseError("No alternatives matched", Position(0, 0, 0)))
    [p, ..rest] -> {
      case p.run(tokens) {
        Ok(result) -> Ok(result)
        Error(_) -> choice_loop(rest, tokens)
      }
    }
  }
}

/// Optional: parse or return empty
pub fn opt(p: Parser) -> Parser {
  Parser(fn(tokens) {
    case p.run(tokens) {
      Ok(result) -> Ok(result)
      Error(_) -> Ok(#(TreeNode("Opt", []), tokens))
    }
  })
}

/// Zero or more repetitions
pub fn rep(p: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(parts, remaining) <- result.try(rep_loop(p, tokens, []))
    Ok(#(TreeNode("Rep", parts), remaining))
  })
}

fn rep_loop(
  p: Parser,
  tokens: List(Token),
  acc: List(ParseTree),
) -> Result(#(List(ParseTree), List(Token)), ParseError) {
  case p.run(tokens) {
    Ok(#(part, remaining)) -> rep_loop(p, remaining, [part, ..acc])
    Error(_) -> Ok(#(acc |> list.reverse, tokens))
  }
}

/// One or more repetitions
pub fn rep1(p: Parser) -> Parser {
  Parser(fn(tokens) {
    use #(first, remaining) <- result.try(p.run(tokens))
    use #(parts, remaining2) <- result.try(rep_loop(p, remaining, [first]))
    Ok(#(TreeNode("Rep1", parts), remaining2))
  })
}

/// Map parser result
pub fn map(p: Parser, f: fn(ParseTree) -> ParseTree) -> Parser {
  Parser(fn(tokens) {
    use #(result, tokens) <- result.try(p.run(tokens))
    Ok(#(f(result), tokens))
  })
}

/// Label a parser result
pub fn label(p: Parser, name: String) -> Parser {
  Parser(fn(tokens) {
    use #(result, tokens) <- result.try(p.run(tokens))
    Ok(#(TreeNode(name, [result]), tokens))
  })
}

// ============================================================================
// RUNNING PARSERS
// ============================================================================

/// Run a parser on a string input
pub fn parse_string(
  parser: Parser,
  input: String,
) -> Result(ParseTree, ParseError) {
  let tokens = tokenize(input)
  case parser.run(tokens) {
    Ok(#(result, remaining)) ->
      case remaining {
        [tok, ..] ->
          Error(ParseError("Unexpected token: " <> tok.value, tok.pos))
        [] -> Ok(result)
      }
    Error(e) -> Error(e)
  }
}
