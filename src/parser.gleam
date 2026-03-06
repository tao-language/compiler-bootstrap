// ============================================================================
// PARSER - Language-Agnostic Parser Combinator Library
// ============================================================================
/// A general-purpose parser combinator library for building recursive descent
/// parsers. Supports both C-style (brace-delimited) and Python-style
/// (indentation-based) languages.
///
/// # Overview
///
/// This library provides:
/// - **Token-based parsing**: Work with pre-tokenized input
/// - **Parser combinators**: Build complex parsers from simple ones
/// - **Error handling**: Graceful error recovery and reporting
/// - **Multiple syntax styles**: Support for braces or indentation
///
/// # Example
///
/// ```gleam
/// import parser
///
/// // Create a simple parser
/// let ident_parser = parser.token(TokIdent)
/// let expr_parser = parser.seq2(ident_parser, ident_parser)
/// ```

import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result

// ============================================================================
// TYPES
// ============================================================================

/// A token with optional position information
pub type Token(token) {
  Token(value: token, pos: Position)
}

/// Source position for error reporting
pub type Position {
  Position(line: Int, column: Int, offset: Int)
}

/// Parser state - tracks current position in token stream
pub type State(token) {
  State(tokens: List(Token(token)), pos: Int)
}

/// A parser that consumes tokens and produces a value
/// Returns Ok((value, new_state)) on success, Error(message) on failure
pub type Parser(token, a) {
  Parser(run: fn(State(token)) -> Result(#(a, State(token)), String))
}

/// Parser configuration for different language styles
pub type Config {
  Config(
    /// Use indentation for block structure (Python-style)
    indent_based: Bool,
    /// Indentation width in spaces
    indent_width: Int,
    /// Token that starts a block (e.g., "{")
    block_start: Option(String),
    /// Token that ends a block (e.g., "}")
    block_end: Option(String),
    /// Token that separates statements (e.g., ";")
    statement_sep: Option(String),
  )
}

// ============================================================================
// CONFIGURATION
// ============================================================================

/// Default configuration for C-style languages (braces, semicolons)
pub fn c_style_config() -> Config {
  Config(
    indent_based: False,
    indent_width: 2,
    block_start: Some("{"),
    block_end: Some("}"),
    statement_sep: Some(";"),
  )
}

/// Configuration for Python-style languages (indentation-based)
pub fn python_style_config() -> Config {
  Config(
    indent_based: True,
    indent_width: 4,
    block_start: None,
    block_end: None,
    statement_sep: None,
  )
}

/// Configuration for OCaml-style languages (begin/end)
pub fn ocaml_style_config() -> Config {
  Config(
    indent_based: False,
    indent_width: 2,
    block_start: Some("begin"),
    block_end: Some("end"),
    statement_sep: Some(";;"),
  )
}

// ============================================================================
// BASIC PARSERS
// ============================================================================

/// Create a parser that matches a specific token
pub fn token(match_fn: fn(token) -> Bool) -> Parser(token, token) {
  Parser(fn(state) {
    case state.tokens {
      [] -> Error("Unexpected end of input")
      [Token(t, _), ..rest] ->
        case match_fn(t) {
          True -> Ok(#(t, State(rest, state.pos + 1)))
          False -> Error("Unexpected token")
        }
    }
  })
}

/// Create a parser that matches a token with a specific value
pub fn token_eq(value: token) -> Parser(token, token) {
  token(fn(t) { t == value })
}

/// Parser that always succeeds with the given value
pub fn pure(value: a) -> Parser(token, a) {
  Parser(fn(state) { Ok(#(value, state)) })
}

/// Parser that always fails with the given message
pub fn fail(message: String) -> Parser(token, a) {
  Parser(fn(_) { Error(message) })
}

/// Parser that consumes no input and returns the current position
pub fn position() -> Parser(token, Position) {
  Parser(fn(state) {
    case state.tokens {
      [] -> Ok(#(Position(0, 0, state.pos), state))
      [Token(_, pos), ..] -> Ok(#(pos, state))
    }
  })
}

// ============================================================================
// SEQUENCE COMBINATORS
// ============================================================================

/// Parse two values in sequence
pub fn seq2(p1: Parser(token, a), p2: Parser(token, b)) -> Parser(token, #(a, b)) {
  Parser(fn(state) {
    use #(v1, state) <- result.try(p1.run(state))
    use #(v2, state) <- result.try(p2.run(state))
    Ok(#(#(v1, v2), state))
  })
}

/// Parse three values in sequence
pub fn seq3(
  p1: Parser(token, a),
  p2: Parser(token, b),
  p3: Parser(token, c),
) -> Parser(token, #(a, b, c)) {
  Parser(fn(state) {
    use #(v1, state) <- result.try(p1.run(state))
    use #(v2, state) <- result.try(p2.run(state))
    use #(v3, state) <- result.try(p3.run(state))
    Ok(#(#(v1, v2, v3), state))
  })
}

/// Parse a value and ignore the result (for separators, etc.)
pub fn ignore_right(p1: Parser(token, a), p2: Parser(token, b)) -> Parser(token, a) {
  Parser(fn(state) {
    use #(v1, state) <- result.try(p1.run(state))
    use #(_, state) <- result.try(p2.run(state))
    Ok(#(v1, state))
  })
}

/// Parse a value and ignore the first result
pub fn ignore_left(p1: Parser(token, a), p2: Parser(token, b)) -> Parser(token, b) {
  Parser(fn(state) {
    use #(_, state) <- result.try(p1.run(state))
    use #(v2, state) <- result.try(p2.run(state))
    Ok(#(v2, state))
  })
}

/// Parse three values, keeping only the middle one (for delimited lists)
pub fn between(
  open: Parser(token, a),
  p: Parser(token, b),
  close: Parser(token, c),
) -> Parser(token, b) {
  ignore_right(ignore_left(open, p), close)
}

// ============================================================================
// CHOICE COMBINATORS
// ============================================================================

/// Try the first parser, if it fails try the second
pub fn or(p1: Parser(token, a), p2: Parser(token, a)) -> Parser(token, a) {
  Parser(fn(state) {
    case p1.run(state) {
      Ok(result) -> Ok(result)
      Error(_) -> p2.run(state)
    }
  })
}

/// Try a list of parsers in order until one succeeds
pub fn choice(parsers: List(Parser(token, a))) -> Parser(token, a) {
  case parsers {
    [] -> fail("No parser succeeded")
    [p, ..rest] -> or(p, choice(rest))
  }
}

// ============================================================================
// REPETITION COMBINATORS
// ============================================================================

/// Parse zero or more occurrences (like regex *)
pub fn many(p: Parser(token, a)) -> Parser(token, List(a)) {
  Parser(fn(state) {
    many_loop(p, state, [])
  })
}

fn many_loop(p: Parser(token, a), state: State(token), acc: List(a)) -> Result(#(List(a), State(token)), String) {
  case p.run(state) {
    Ok(#(v, rest)) -> many_loop(p, rest, [v, ..acc])
    Error(_) -> Ok(#(list.reverse(acc), state))
  }
}

/// Parse one or more occurrences (like regex +)
pub fn many1(p: Parser(token, a)) -> Parser(token, List(a)) {
  Parser(fn(state) {
    use #(v, rest) <- result.try(p.run(state))
    case many_loop(p, rest, []) {
      Ok(#(vs, rest2)) -> Ok(#([v, ..vs], rest2))
      Error(e) -> Error(e)
    }
  })
}

/// Parse zero or more occurrences separated by a separator
pub fn sep_by(p: Parser(token, a), sep: Parser(token, b)) -> Parser(token, List(a)) {
  or(
    sep_by1(p, sep),
    pure([]),
  )
}

/// Parse one or more occurrences separated by a separator
pub fn sep_by1(p: Parser(token, a), sep: Parser(token, b)) -> Parser(token, List(a)) {
  Parser(fn(state) {
    use #(v, rest) <- result.try(p.run(state))
    sep_by1_loop(p, sep, rest, [v])
  })
}

fn sep_by1_loop(
  p: Parser(token, a),
  sep: Parser(token, b),
  state: State(token),
  acc: List(a),
) -> Result(#(List(a), State(token)), String) {
  case sep.run(state) {
    Ok(#(_, sep_state)) ->
      case p.run(sep_state) {
        Ok(#(v2, rest2)) -> sep_by1_loop(p, sep, rest2, [v2, ..acc])
        Error(_) -> Ok(#(list.reverse(acc), state))
      }
    Error(_) -> Ok(#(list.reverse(acc), state))
  }
}

// ============================================================================
// OPTIONAL COMBINATORS
// ============================================================================

/// Parse an optional value, returns None if parser fails
pub fn opt(p: Parser(token, a)) -> Parser(token, Option(a)) {
  Parser(fn(state) {
    case p.run(state) {
      Ok(#(v, rest)) -> Ok(#(Some(v), rest))
      Error(_) -> Ok(#(None, state))
    }
  })
}

// ============================================================================
// TRANSFORMATION COMBINATORS
// ============================================================================

/// Transform the result of a parser
pub fn map(p: Parser(token, a), f: fn(a) -> b) -> Parser(token, b) {
  Parser(fn(state) {
    case p.run(state) {
      Ok(#(v, rest)) -> Ok(#(f(v), rest))
      Error(e) -> Error(e)
    }
  })
}

/// Transform the result with a function that can fail
pub fn and_then(p: Parser(token, a), f: fn(a) -> Result(b, String)) -> Parser(token, b) {
  Parser(fn(state) {
    use #(v, rest) <- result.try(p.run(state))
    use v2 <- result.try(f(v))
    Ok(#(v2, rest))
  })
}

// ============================================================================
// BLOCK PARSING
// ============================================================================

/// Parse a block delimited by start/end tokens
pub fn block(
  start: Parser(token, a),
  body: Parser(token, b),
  end: Parser(token, c),
) -> Parser(token, b) {
  between(start, body, end)
}

/// Parse an indentation-based block
pub fn indent_block(
  indent: Parser(token, Int),
  body: Parser(token, b),
  dedent: Parser(token, Int),
) -> Parser(token, b) {
  Parser(fn(state) {
    use #(_, state) <- result.try(indent.run(state))
    use #(v, state) <- result.try(body.run(state))
    use #(_, state) <- result.try(dedent.run(state))
    Ok(#(v, state))
  })
}

// ============================================================================
// LIST PARSING
// ============================================================================

/// Parse a comma-separated list in braces: { x, y, z }
pub fn braced_list(
  open: Parser(token, a),
  p: Parser(token, b),
  sep: Parser(token, c),
  close: Parser(token, d),
) -> Parser(token, List(b)) {
  between(open, sep_by(p, sep), close)
}

// ============================================================================
// RUNNING PARSERS
// ============================================================================

/// Run a parser on a list of tokens
pub fn run(parser: Parser(token, a), tokens: List(Token(token))) -> Result(a, String) {
  let state = State(tokens, 0)
  case parser.run(state) {
    Ok(#(value, _)) -> Ok(value)
    Error(e) -> Error(e)
  }
}

/// Run a parser and return both the result and remaining tokens
pub fn run_with_remaining(
  parser: Parser(token, a),
  tokens: List(Token(token)),
) -> Result(#(a, List(Token(token))), String) {
  let state = State(tokens, 0)
  case parser.run(state) {
    Ok(#(value, rest_state)) -> Ok(#(value, rest_state.tokens))
    Error(e) -> Error(e)
  }
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

/// Add context to an error message
pub fn with_context(parser: Parser(token, a), context: String) -> Parser(token, a) {
  Parser(fn(state) {
    case parser.run(state) {
      Ok(result) -> Ok(result)
      Error(e) -> Error(context <> ": " <> e)
    }
  })
}

/// Try to parse, if it fails consume one token and try again
pub fn recover(parser: Parser(token, a)) -> Parser(token, Option(a)) {
  Parser(fn(state) {
    case parser.run(state) {
      Ok(#(v, rest)) -> Ok(#(Some(v), rest))
      Error(_) ->
        case state.tokens {
          [] -> Ok(#(None, state))
          [_, ..rest] -> Ok(#(None, State(rest, state.pos + 1)))
        }
    }
  })
}
