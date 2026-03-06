// ============================================================================
// CORE LANGUAGE PARSER
// ============================================================================
/// Simple recursive descent parser for the core language.
///
/// This module defines the grammar and parsing logic specific to the core
/// language using a straightforward recursive descent approach.
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

import core/core
import gleam/int
import gleam/list
import gleam/result
import gleam/string

// ============================================================================
// CORE TOKENS
// ============================================================================

/// Token types specific to the core language
pub type CoreToken {
  Ident(String)
  Constructor(String)
  Integer(Int)
  TypeKeyword(Int)
  LitType(core.LiteralType)
  Match
  With
  Arrow
  Colon
  Comma
  LParen
  RParen
  LBrace
  RBrace
  Underscore
  Hole
}

// ============================================================================
// LEXER
// ============================================================================

/// Convert source code to core language tokens
pub fn tokenize(source: String) -> List(CoreToken) {
  let chars =
    source
    |> string.to_utf_codepoints
    |> list.map(string.utf_codepoint_to_int)
  do_tokenize(chars, []) |> list.reverse
}

fn do_tokenize(chars: List(Int), acc: List(CoreToken)) -> List(CoreToken) {
  case chars {
    [] -> [Hole, ..acc]
    [c, ..rest] ->
      case c {
        // Whitespace
        32 | 10 | 13 | 9 -> do_tokenize(skip_whitespace(rest), acc)
        
        // Comment
        47 ->
          case rest {
            [47, ..r] -> do_tokenize(skip_comment(r), acc)
            _ -> do_tokenize(rest, acc)
          }
        
        // Punctuation
        40 -> do_tokenize(rest, [LParen, ..acc])
        41 -> do_tokenize(rest, [RParen, ..acc])
        123 -> do_tokenize(rest, [LBrace, ..acc])
        125 -> do_tokenize(rest, [RBrace, ..acc])
        58 -> do_tokenize(rest, [Colon, ..acc])
        44 -> do_tokenize(rest, [Comma, ..acc])
        95 -> do_tokenize(rest, [Underscore, ..acc])
        63 -> do_tokenize(rest, [Hole, ..acc])
        
        // Arrow
        61 ->
          case rest {
            [62, ..r] -> do_tokenize(r, [Arrow, ..acc])
            _ -> do_tokenize(rest, acc)
          }
        
        // Identifiers and keywords
        _ if c >= 97 && c <= 122 -> tokenize_identifier(chars, acc)
        
        // Constructors
        _ if c >= 65 && c <= 90 -> tokenize_constructor(chars, acc)
        
        // Numbers
        _ if c >= 48 && c <= 57 -> tokenize_number(chars, acc)
        
        // Unknown
        _ -> do_tokenize(rest, acc)
      }
  }
}

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

fn skip_comment(chars: List(Int)) -> List(Int) {
  case chars {
    [] -> []
    [10, ..rest] -> rest
    [_, ..rest] -> skip_comment(rest)
  }
}

fn tokenize_identifier(chars: List(Int), acc: List(CoreToken)) -> List(CoreToken) {
  let #(name, rest) = take_while(chars, is_alphanumeric, "")
  let keyword = case name {
    "match" -> Match
    "with" -> With
    "Type" | "Type0" -> TypeKeyword(0)
    "Type1" -> TypeKeyword(1)
    "Type2" -> TypeKeyword(2)
    "Type3" -> TypeKeyword(3)
    "Type4" -> TypeKeyword(4)
    "I32" -> LitType(core.I32T)
    "I64" -> LitType(core.I64T)
    "U32" -> LitType(core.U32T)
    "U64" -> LitType(core.U64T)
    "F32" -> LitType(core.F32T)
    "F64" -> LitType(core.F64T)
    _ -> Ident(name)
  }
  do_tokenize(rest, [keyword, ..acc])
}

fn tokenize_constructor(chars: List(Int), acc: List(CoreToken)) -> List(CoreToken) {
  let #(name, rest) = take_while(chars, is_alphanumeric, "")
  let token = case name {
    "Type" -> TypeKeyword(0)
    "Type0" -> TypeKeyword(0)
    "Type1" -> TypeKeyword(1)
    "Type2" -> TypeKeyword(2)
    "Type3" -> TypeKeyword(3)
    "Type4" -> TypeKeyword(4)
    _ -> Constructor(name)
  }
  do_tokenize(rest, [token, ..acc])
}

fn tokenize_number(chars: List(Int), acc: List(CoreToken)) -> List(CoreToken) {
  let #(int_part, rest) = take_while(chars, is_digit, "")
  case int.parse(int_part) {
    Ok(i) -> do_tokenize(rest, [Integer(i), ..acc])
    Error(_) -> do_tokenize(rest, acc)
  }
}

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

fn is_alphanumeric(c: Int) -> Bool {
  c >= 97 && c <= 122 || c >= 65 && c <= 90 || c >= 48 && c <= 57
}

fn is_digit(c: Int) -> Bool {
  c >= 48 && c <= 57
}

fn char_to_string(c: Int) -> String {
  case string.utf_codepoint(c) {
    Ok(cp) -> string.from_utf_codepoints([cp])
    Error(_) -> ""
  }
}

// ============================================================================
// PARSER STATE
// ============================================================================

type ParserState {
  ParserState(tokens: List(CoreToken), pos: Int)
}

// ============================================================================
// PARSER
// ============================================================================

/// Parse source code into a Term
pub fn parse_source(source: String) -> Result(core.Term, String) {
  let tokens = tokenize(source)
  let state = ParserState(tokens, 0)
  case parse_term(state) {
    Ok(#(term, _)) -> Ok(term)
    Error(e) -> Error(e)
  }
}

fn peek(state: ParserState) -> Result(CoreToken, String) {
  case state.tokens {
    [] -> Error("Unexpected end of input")
    [t, ..] -> Ok(t)
  }
}

fn advance(state: ParserState) -> ParserState {
  case state.tokens {
    [] -> state
    [_, ..rest] -> ParserState(rest, state.pos + 1)
  }
}

fn expect(state: ParserState, expected: CoreToken) -> Result(ParserState, String) {
  case peek(state) {
    Ok(t) if t == expected -> Ok(advance(state))
    Ok(_) -> Error("Unexpected token")
    Error(e) -> Error(e)
  }
}

fn parse_term(state: ParserState) -> Result(#(core.Term, ParserState), String) {
  let span = core.Span("parsed", 0, 0)
  
  case peek(state) {
    Ok(Match) -> parse_match(state, span)
    _ -> parse_lambda(state, span)
  }
}

fn parse_match(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use state <- result.try(expect(state, Match))
  use #(arg, state) <- result.try(parse_term(state))
  use state <- result.try(expect(state, With))
  use state <- result.try(expect(state, LBrace))
  use #(cases, state) <- result.try(parse_cases(state, [], span))
  use state <- result.try(expect(state, RBrace))
  
  let motive = core.Term(core.Lam("_", core.Term(core.Typ(0), span)), span)
  Ok(#(core.Term(core.Match(arg, motive, cases), span), state))
}

fn parse_cases(
  state: ParserState,
  acc: List(core.Case),
  span: core.Span,
) -> Result(#(List(core.Case), ParserState), String) {
  case peek(state) {
    Ok(RBrace) -> Ok(#(list.reverse(acc), state))
    _ -> {
      use #(c, state) <- result.try(parse_case(state, span))
      parse_cases(state, [c, ..acc], span)
    }
  }
}

fn parse_case(state: ParserState, span: core.Span) -> Result(#(core.Case, ParserState), String) {
  use #(pattern, state) <- result.try(parse_pattern(state))
  use state <- result.try(expect(state, Arrow))
  use #(body, state) <- result.try(parse_term(state))
  Ok(#(core.Case(pattern, body, span), state))
}

fn parse_lambda(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  case peek(state) {
    Ok(LParen) -> {
      use state <- result.try(expect(state, LParen))
      use #(name, state) <- result.try(parse_ident(state))
      use state <- result.try(expect(state, Colon))
      use #(_in_ty, state) <- result.try(parse_term(state))
      use state <- result.try(expect(state, RParen))
      use state <- result.try(expect(state, Arrow))
      use #(body, state) <- result.try(parse_term(state))
      Ok(#(core.Term(core.Lam(name, body), span), state))
    }
    _ -> parse_application(state, span)
  }
}

fn parse_application(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use #(fun, state) <- result.try(parse_atom(state, span))
  
  case peek(state) {
    Ok(LParen) -> {
      use state <- result.try(expect(state, LParen))
      use #(arg, state) <- result.try(parse_term(state))
      use state <- result.try(expect(state, RParen))
      Ok(#(core.Term(core.App(fun, arg), span), state))
    }
    _ -> Ok(#(fun, state))
  }
}

fn parse_atom(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  case peek(state) {
    Ok(LBrace) -> parse_record(state, span)
    Ok(Constructor(_)) -> parse_constructor(state, span)
    Ok(Hole) -> parse_hole(state, span)
    Ok(LitType(_)) -> parse_literal_type(state, span)
    Ok(Integer(_)) -> parse_literal(state, span)
    Ok(TypeKeyword(_)) -> parse_type(state, span)
    Ok(Ident(_)) -> parse_variable(state, span)
    _ -> Error("Unexpected token")
  }
}

fn parse_record(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use state <- result.try(expect(state, LBrace))
  use #(fields, state) <- result.try(parse_fields(state, [], span))
  use state <- result.try(expect(state, RBrace))
  Ok(#(core.Term(core.Rcd(fields), span), state))
}

fn parse_fields(
  state: ParserState,
  acc: List(#(String, core.Term)),
  span: core.Span,
) -> Result(#(List(#(String, core.Term)), ParserState), String) {
  case peek(state) {
    Ok(RBrace) -> Ok(#(list.reverse(acc), state))
    _ -> {
      use #(name, state) <- result.try(parse_ident(state))
      use state <- result.try(expect(state, Colon))
      use #(value, state) <- result.try(parse_term(state))
      
      let state = case peek(state) {
        Ok(Comma) -> advance(state)
        _ -> state
      }
      parse_fields(state, [#(name, value), ..acc], span)
    }
  }
}

fn parse_constructor(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use #(tag, state) <- result.try(parse_constructor_name(state))
  use state <- result.try(expect(state, LParen))
  use #(arg, state) <- result.try(parse_term(state))
  use state <- result.try(expect(state, RParen))
  Ok(#(core.Term(core.Ctr(tag, arg), span), state))
}

fn parse_hole(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use state <- result.try(expect(state, Hole))
  Ok(#(core.Term(core.Hole(0), span), state))
}

fn parse_literal_type(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  case peek(state) {
    Ok(LitType(lt)) -> {
      let state = advance(state)
      Ok(#(core.Term(core.LitT(lt), span), state))
    }
    _ -> Error("Expected literal type")
  }
}

fn parse_literal(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  case peek(state) {
    Ok(Integer(i)) -> {
      let state = advance(state)
      Ok(#(core.Term(core.Lit(core.I32(i)), span), state))
    }
    _ -> Error("Expected literal")
  }
}

fn parse_type(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  case peek(state) {
    Ok(TypeKeyword(k)) -> {
      let state = advance(state)
      Ok(#(core.Term(core.Typ(k), span), state))
    }
    _ -> Error("Expected type")
  }
}

fn parse_variable(state: ParserState, span: core.Span) -> Result(#(core.Term, ParserState), String) {
  use #(_name, state) <- result.try(parse_ident(state))
  // Placeholder - name resolution happens later
  Ok(#(core.Term(core.Var(0), span), state))
}

fn parse_ident(state: ParserState) -> Result(#(String, ParserState), String) {
  case peek(state) {
    Ok(Ident(name)) -> Ok(#(name, advance(state)))
    _ -> Error("Expected identifier")
  }
}

fn parse_constructor_name(state: ParserState) -> Result(#(String, ParserState), String) {
  case peek(state) {
    Ok(Constructor(name)) -> Ok(#(name, advance(state)))
    _ -> Error("Expected constructor")
  }
}

fn parse_pattern(state: ParserState) -> Result(#(core.Pattern, ParserState), String) {
  case peek(state) {
    Ok(Underscore) -> {
      let state = advance(state)
      Ok(#(core.PAny, state))
    }
    Ok(Ident(name)) -> {
      let state = advance(state)
      Ok(#(core.PAs(core.PAny, name), state))
    }
    Ok(Constructor(_)) -> {
      use #(tag, state) <- result.try(parse_constructor_name(state))
      use state <- result.try(expect(state, LParen))
      use #(arg, state) <- result.try(parse_pattern(state))
      use state <- result.try(expect(state, RParen))
      Ok(#(core.PCtr(tag, arg), state))
    }
    _ -> Error("Expected pattern")
  }
}
