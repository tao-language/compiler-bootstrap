// ============================================================================
// PARSER - Simple Recursive Descent Parser
// ============================================================================
/// A simple recursive descent parser for the core language.
///
/// This parser converts source code into an abstract syntax tree (AST).
/// It uses a straightforward recursive descent approach without complex
/// parser combinators or generator frameworks.
///
/// # TypeScript-like Syntax
///
/// ```typescript
/// Type0
/// (x: A) => x
/// f(x)
/// { x: 1, y: 2 }
/// match x with { A => 1 }
/// ```

import core
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string

// ============================================================================
// TOKENS
// ============================================================================

/// Token types for the core language
pub type Token {
  /// Identifier: x, y, f
  TokIdent(String)
  /// Constructor: Cons, Nil, True, False
  TokConstructor(String)
  /// Integer literal: 42
  TokInteger(Int)
  /// Type keyword: Type, Type0, Type1
  TokType(Int)
  /// Literal type: I32, F64
  TokLitType(core.LiteralType)
  /// Keywords
  TokMatch
  TokWith
  TokArrow
  TokColon
  TokComma
  TokLParen
  TokRParen
  TokLBrace
  TokRBrace
  TokUnderscore
  TokHole
  /// End of file
  TokEOF
}

// ============================================================================
// LEXER
// ============================================================================

/// Convert source code to a list of tokens
pub fn tokenize(source: String) -> List(Token) {
  let chars =
    string.to_utf_codepoints(source) |> list.map(string.utf_codepoint_to_int)
  do_tokenize(chars, []) |> list.reverse
}

fn do_tokenize(chars: List(Int), acc: List(Token)) -> List(Token) {
  case chars {
    [] -> [TokEOF, ..acc]
    [c, ..rest] ->
      case c {
        // Whitespace: space, newline, tab, carriage return
        32 | 10 | 13 | 9 -> do_tokenize(skip_whitespace(rest), acc)
        
        // Comment: //
        47 ->
          case rest {
            [47, ..r] -> do_tokenize(skip_comment(r), acc)
            _ -> do_tokenize(rest, acc)
          }
        
        // Punctuation and symbols
        40 -> do_tokenize(rest, [TokLParen, ..acc])
        41 -> do_tokenize(rest, [TokRParen, ..acc])
        123 -> do_tokenize(rest, [TokLBrace, ..acc])
        125 -> do_tokenize(rest, [TokRBrace, ..acc])
        58 -> do_tokenize(rest, [TokColon, ..acc])
        44 -> do_tokenize(rest, [TokComma, ..acc])
        95 -> do_tokenize(rest, [TokUnderscore, ..acc])
        63 -> do_tokenize(rest, [TokHole, ..acc])
        
        // Arrow: =>
        61 ->
          case rest {
            [62, ..r] -> do_tokenize(r, [TokArrow, ..acc])
            _ -> do_tokenize(rest, acc)
          }
        
        // Lowercase: identifier or keyword
        _ if c >= 97 && c <= 122 -> tokenize_identifier(chars, acc)
        
        // Uppercase: constructor or Type keyword
        _ if c >= 65 && c <= 90 -> tokenize_constructor(chars, acc)
        
        // Digit: number
        _ if c >= 48 && c <= 57 -> tokenize_number(chars, acc)
        
        // Unknown: skip
        _ -> do_tokenize(rest, acc)
      }
  }
}

/// Skip whitespace characters
fn skip_whitespace(chars: List(Int)) -> List(Int) {
  case chars {
    [] -> []
    [c, ..rest] ->
      case c {
        32 | 10 | 13 | 9 -> skip_whitespace(rest)
        _ -> chars
      }
  }
}

/// Skip comment until end of line
fn skip_comment(chars: List(Int)) -> List(Int) {
  case chars {
    [] -> []
    [10, ..rest] -> rest
    [_, ..rest] -> skip_comment(rest)
  }
}

/// Tokenize an identifier or keyword
fn tokenize_identifier(chars: List(Int), acc: List(Token)) -> List(Token) {
  let #(name, rest) = take_while(chars, is_alphanumeric, "")
  let keyword = case name {
    "match" -> TokMatch
    "with" -> TokWith
    "Type" | "Type0" -> TokType(0)
    "Type1" -> TokType(1)
    "Type2" -> TokType(2)
    "Type3" -> TokType(3)
    "Type4" -> TokType(4)
    "I32" -> TokLitType(core.I32T)
    "I64" -> TokLitType(core.I64T)
    "U32" -> TokLitType(core.U32T)
    "U64" -> TokLitType(core.U64T)
    "F32" -> TokLitType(core.F32T)
    "F64" -> TokLitType(core.F64T)
    _ -> TokIdent(name)
  }
  do_tokenize(rest, [keyword, ..acc])
}

/// Tokenize a constructor or Type keyword
fn tokenize_constructor(chars: List(Int), acc: List(Token)) -> List(Token) {
  let #(name, rest) = take_while(chars, is_alphanumeric, "")
  let token = case name {
    "Type" -> TokType(0)
    "Type0" -> TokType(0)
    "Type1" -> TokType(1)
    "Type2" -> TokType(2)
    "Type3" -> TokType(3)
    "Type4" -> TokType(4)
    _ -> TokConstructor(name)
  }
  do_tokenize(rest, [token, ..acc])
}

/// Tokenize a number (integer only for simplicity)
fn tokenize_number(chars: List(Int), acc: List(Token)) -> List(Token) {
  let #(int_part, rest) = take_while(chars, is_digit, "")
  case int.parse(int_part) {
    Ok(i) -> do_tokenize(rest, [TokInteger(i), ..acc])
    Error(_) -> do_tokenize(rest, acc)
  }
}

/// Take characters while predicate is true
fn take_while(
  chars: List(Int),
  pred: fn(Int) -> Bool,
  acc: String,
) -> #(String, List(Int)) {
  case chars {
    [] -> #(acc, [])
    [c, ..rest] ->
      case pred(c) {
        True -> take_while(rest, pred, acc <> char_to_string(c))
        False -> #(acc, chars)
      }
  }
}

/// Check if character is alphanumeric
fn is_alphanumeric(c: Int) -> Bool {
  c >= 97 && c <= 122 || c >= 65 && c <= 90 || c >= 48 && c <= 57
}

/// Check if character is a digit
fn is_digit(c: Int) -> Bool {
  c >= 48 && c <= 57
}

/// Convert integer to single-character string
fn char_to_string(c: Int) -> String {
  case string.utf_codepoint(c) {
    Ok(cp) -> string.from_utf_codepoints([cp])
    Error(_) -> ""
  }
}

// ============================================================================
// PARSER
// ============================================================================

type Parser {
  Parser(tokens: List(Token))
}

/// Peek at the current token without consuming it
fn peek(parser: Parser) -> Option(Token) {
  case parser.tokens {
    [] -> None
    [t, ..] -> Some(t)
  }
}

/// Advance to the next token
fn advance(parser: Parser) -> Parser {
  case parser.tokens {
    [] -> parser
    [_, ..rest] -> Parser(rest)
  }
}

/// Expect a specific token, return error if not found
fn expect(parser: Parser, expected: Token) -> Result(Parser, String) {
  case peek(parser) {
    Some(t) if t == expected -> Ok(advance(parser))
    Some(_) -> Error("Unexpected token")
    None -> Error("Unexpected end of input")
  }
}

/// Parse source code into a Term
pub fn parse_source(source: String) -> Result(core.Term, String) {
  let tokens = tokenize(source)
  let parser = Parser(tokens)
  case parse_term(parser) {
    Ok(#(term, _)) -> Ok(term)
    Error(e) -> Error(e)
  }
}

/// Parse a term (entry point for term parsing)
fn parse_term(parser: Parser) -> Result(#(core.Term, Parser), String) {
  let span = core.Span("parsed", 0, 0)
  
  case peek(parser) {
    Some(TokMatch) -> parse_match(parser, span)
    _ -> parse_lambda(parser, span)
  }
}

/// Parse match expression: match x with { A => 1 }
fn parse_match(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use parser <- result.try(expect(parser, TokMatch))
  use #(arg, parser) <- result.try(parse_term(parser))
  use parser <- result.try(expect(parser, TokWith))
  use parser <- result.try(expect(parser, TokLBrace))
  use #(cases, parser) <- result.try(parse_cases(parser, []))
  use _parser <- result.try(expect(parser, TokRBrace))
  
  let motive = core.Term(core.Lam("_", core.Term(core.Typ(0), span)), span)
  Ok(#(core.Term(core.Match(arg, motive, cases), span), parser))
}

/// Parse match cases
fn parse_cases(
  parser: Parser,
  acc: List(core.Case),
) -> Result(#(List(core.Case), Parser), String) {
  case peek(parser) {
    Some(TokRBrace) -> Ok(#(list.reverse(acc), parser))
    Some(_) -> {
      use #(c, parser) <- result.try(parse_case(parser))
      parse_cases(parser, [c, ..acc])
    }
    None -> Error("Unexpected end of input")
  }
}

/// Parse a single case: pattern => body
fn parse_case(parser: Parser) -> Result(#(core.Case, Parser), String) {
  let span = core.Span("parsed", 0, 0)
  use #(pattern, parser) <- result.try(parse_pattern(parser))
  use parser <- result.try(expect(parser, TokArrow))
  use #(body, parser) <- result.try(parse_term(parser))
  Ok(#(core.Case(pattern, body, span), parser))
}

/// Parse lambda: (x: Type) => body
fn parse_lambda(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  case peek(parser) {
    Some(TokLParen) -> {
      use parser <- result.try(expect(parser, TokLParen))
      use #(name, parser) <- result.try(parse_identifier(parser))
      use parser <- result.try(expect(parser, TokColon))
      use #(_in_ty, _parser) <- result.try(parse_term(parser))
      use parser <- result.try(expect(parser, TokRParen))
      use parser <- result.try(expect(parser, TokArrow))
      use #(body, parser) <- result.try(parse_term(parser))

      Ok(#(core.Term(core.Lam(name, body), span), parser))
    }
    _ -> parse_application(parser, span)
  }
}

/// Parse application: f(x)
fn parse_application(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use #(fun, parser) <- result.try(parse_atom(parser, span))
  
  case peek(parser) {
    Some(TokLParen) -> {
      use parser <- result.try(expect(parser, TokLParen))
      use #(arg, parser) <- result.try(parse_term(parser))
      use _parser <- result.try(expect(parser, TokRParen))
      Ok(#(core.Term(core.App(fun, arg), span), parser))
    }
    _ -> Ok(#(fun, parser))
  }
}

/// Parse atomic expressions
fn parse_atom(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  case peek(parser) {
    Some(TokLBrace) -> parse_record(parser, span)
    Some(TokConstructor(_)) -> parse_constructor(parser, span)
    Some(TokLParen) -> parse_annotated(parser, span)
    Some(TokHole) -> parse_hole(parser, span)
    Some(TokLitType(_)) -> parse_literal_type(parser, span)
    Some(TokInteger(_)) -> parse_literal(parser, span)
    Some(TokType(_)) -> parse_type(parser, span)
    Some(TokIdent(_)) -> parse_variable(parser, span)
    _ -> Error("Unexpected token")
  }
}

/// Parse annotated term: (term: type)
fn parse_annotated(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use parser <- result.try(expect(parser, TokLParen))
  use #(term, parser) <- result.try(parse_term(parser))
  use parser <- result.try(expect(parser, TokColon))
  use #(typ, parser) <- result.try(parse_term(parser))
  use parser <- result.try(expect(parser, TokRParen))
  Ok(#(core.Term(core.Ann(term, typ), span), parser))
}

/// Parse record: { x: 1, y: 2 }
fn parse_record(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use parser <- result.try(expect(parser, TokLBrace))
  use #(fields, parser) <- result.try(parse_fields(parser, []))
  use parser <- result.try(expect(parser, TokRBrace))
  Ok(#(core.Term(core.Rcd(fields), span), parser))
}

/// Parse record fields
fn parse_fields(
  parser: Parser,
  acc: List(#(String, core.Term)),
) -> Result(#(List(#(String, core.Term)), Parser), String) {
  case peek(parser) {
    Some(TokRBrace) -> Ok(#(list.reverse(acc), parser))
    Some(_) -> {
      use #(name, parser) <- result.try(parse_identifier(parser))
      use parser <- result.try(expect(parser, TokColon))
      use #(value, parser) <- result.try(parse_term(parser))

      let parser = case peek(parser) {
        Some(TokComma) -> advance(parser)
        _ -> parser
      }
      parse_fields(parser, [#(name, value), ..acc])
    }
    None -> Error("Unexpected end of input")
  }
}

/// Parse constructor: Cons(x)
fn parse_constructor(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use #(tag, parser) <- result.try(parse_constructor_name(parser))
  use parser <- result.try(expect(parser, TokLParen))
  use #(arg, parser) <- result.try(parse_term(parser))
  use parser <- result.try(expect(parser, TokRParen))
  Ok(#(core.Term(core.Ctr(tag, arg), span), parser))
}

/// Parse hole: ?
fn parse_hole(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use parser <- result.try(expect(parser, TokHole))
  Ok(#(core.Term(core.Hole(0), span), parser))
}

/// Parse literal type: I32
fn parse_literal_type(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  case peek(parser) {
    Some(TokLitType(t)) -> {
      let term = core.Term(core.LitT(t), span)
      Ok(#(term, advance(parser)))
    }
    _ -> Error("Expected literal type")
  }
}

/// Parse literal: 42
fn parse_literal(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  case peek(parser) {
    Some(TokInteger(i)) -> {
      let term = core.Term(core.Lit(core.I32(i)), span)
      Ok(#(term, advance(parser)))
    }
    _ -> Error("Expected literal")
  }
}

/// Parse type: Type, Type0, Type1
fn parse_type(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  case peek(parser) {
    Some(TokType(k)) -> {
      let term = core.Term(core.Typ(k), span)
      Ok(#(term, advance(parser)))
    }
    _ -> Error("Expected type")
  }
}

/// Parse variable: x
fn parse_variable(parser: Parser, span: core.Span) -> Result(#(core.Term, Parser), String) {
  use #(_name, parser) <- result.try(parse_identifier(parser))
  // Placeholder - name resolution happens later
  let term = core.Term(core.Var(0), span)
  Ok(#(term, parser))
}

/// Parse identifier
fn parse_identifier(parser: Parser) -> Result(#(String, Parser), String) {
  case peek(parser) {
    Some(TokIdent(name)) -> Ok(#(name, advance(parser)))
    _ -> Error("Expected identifier")
  }
}

/// Parse constructor name
fn parse_constructor_name(parser: Parser) -> Result(#(String, Parser), String) {
  case peek(parser) {
    Some(TokConstructor(name)) -> Ok(#(name, advance(parser)))
    _ -> Error("Expected constructor")
  }
}

/// Parse pattern
fn parse_pattern(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  case peek(parser) {
    Some(TokUnderscore) -> Ok(#(core.PAny, advance(parser)))
    Some(TokLBrace) -> parse_pattern_record(parser)
    Some(TokConstructor(_)) -> parse_pattern_constructor(parser)
    Some(TokLitType(_)) -> parse_pattern_literal_type(parser)
    Some(TokInteger(_)) -> parse_pattern_literal(parser)
    Some(TokType(_)) -> parse_pattern_type(parser)
    Some(TokIdent(name)) -> Ok(#(core.PAs(core.PAny, name), advance(parser)))
    _ -> Error("Expected pattern")
  }
}

/// Parse pattern record: { x: p }
fn parse_pattern_record(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  use parser <- result.try(expect(parser, TokLBrace))
  use #(fields, parser) <- result.try(parse_pattern_fields(parser, []))
  use parser <- result.try(expect(parser, TokRBrace))
  Ok(#(core.PRcd(fields), parser))
}

/// Parse pattern fields
fn parse_pattern_fields(
  parser: Parser,
  acc: List(#(String, core.Pattern)),
) -> Result(#(List(#(String, core.Pattern)), Parser), String) {
  case peek(parser) {
    Some(TokRBrace) -> Ok(#(list.reverse(acc), parser))
    Some(_) -> {
      use #(name, parser) <- result.try(parse_identifier(parser))
      use parser <- result.try(expect(parser, TokColon))
      use #(pattern, parser) <- result.try(parse_pattern(parser))

      let parser = case peek(parser) {
        Some(TokComma) -> advance(parser)
        _ -> parser
      }
      parse_pattern_fields(parser, [#(name, pattern), ..acc])
    }
    None -> Error("Unexpected end of input")
  }
}

/// Parse pattern constructor: Cons(p)
fn parse_pattern_constructor(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  use #(tag, parser) <- result.try(parse_constructor_name(parser))
  use parser <- result.try(expect(parser, TokLParen))
  use #(arg, parser) <- result.try(parse_pattern(parser))
  use parser <- result.try(expect(parser, TokRParen))
  Ok(#(core.PCtr(tag, arg), parser))
}

/// Parse pattern literal type
fn parse_pattern_literal_type(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  case peek(parser) {
    Some(TokLitType(t)) -> Ok(#(core.PLitT(t), advance(parser)))
    _ -> Error("Expected literal type")
  }
}

/// Parse pattern literal
fn parse_pattern_literal(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  case peek(parser) {
    Some(TokInteger(i)) -> Ok(#(core.PLit(core.I32(i)), advance(parser)))
    _ -> Error("Expected literal")
  }
}

/// Parse pattern type
fn parse_pattern_type(parser: Parser) -> Result(#(core.Pattern, Parser), String) {
  case peek(parser) {
    Some(TokType(k)) -> Ok(#(core.PTyp(k), advance(parser)))
    _ -> Error("Expected type")
  }
}
