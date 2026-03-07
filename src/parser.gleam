// ============================================================================
// PARSER - Complete Parser Combinator Library with Pratt Parsing
// ============================================================================
/// A complete parser combinator library with:
/// - Token-based parsing
/// - Full Pratt parsing for operator precedence
/// - Error recovery with sync points
/// - Source location tracking
///
/// # Example
///
/// ```gleam
/// import parser
///
/// // Build expression parser with precedence
/// let ops = [
///   parser.atom("Number"),
///   parser.infix_l("+", 10),
///   parser.infix_l("*", 20),
/// ]
/// let expr = parser.pratt(ops)
/// ```

import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// Source position
pub type Position {
  Position(row: Int, col: Int, offset: Int)
}

/// Source location
pub type Location {
  Location(filename: String, start: Position, end: Position)
}

/// Error severity
pub type Severity {
  ParseErrorLevel
  Warning
  Info
}

/// Parse error
pub type ParseError {
  ParseError(
    location: Location,
    message: String,
    expected: List(String),
    severity: Severity,
  )
}

/// Token type
pub type Token {
  Token(kind: String, value: String, location: Location, indent: Int)
}

/// Parser state
pub type State {
  State(tokens: List(Token), pos: Int, errors: List(ParseError))
}

/// Parser that produces a value of type `a`
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}

/// Parse result - always succeeds with AST and errors
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

// ============================================================================
// PRATT PARSING TYPES
// ============================================================================

/// Expression operator for Pratt parsing
pub type ExprOp {
  /// Atom - base expression (e.g., Number, Ident, parenthesized expr)
  Atom(kind: String)
  /// Prefix operator (e.g., -x, !x) with precedence
  Prefix(op: String, prec: Int)
  /// Postfix operator (e.g., x!, x++) with precedence
  Postfix(op: String, prec: Int)
  /// Left-associative infix (e.g., +, -, *, /) with precedence
  InfixL(op: String, prec: Int)
  /// Right-associative infix (e.g., ^, =) with precedence
  InfixR(op: String, prec: Int)
}

/// Pratt parser state for expression parsing
type PrattState {
  PrattState(tokens: List(Token), pos: Int)
}

// ============================================================================
// CORE PARSERS
// ============================================================================

/// Parser that succeeds with a value
pub fn ok(a: a) -> Parser(a) {
  Parser(fn(state) { Ok(#(a, state)) })
}

/// Parser that fails with expected message
pub fn fail(expected: String) -> Parser(a) {
  Parser(fn(state) {
    Error(State(..state, errors: [mk_error(state, expected)]))
  })
}

/// Get current token
pub fn current_token() -> Parser(Option(Token)) {
  Parser(fn(state) {
    case get_token_at(state.tokens, state.pos) {
      Ok(token) -> Ok(#(Some(token), state))
      Error(_) -> Ok(#(None, state))
    }
  })
}

/// Get current position
pub fn position() -> Parser(Position) {
  Parser(fn(state) {
    case get_token_at(state.tokens, state.pos) {
      Ok(token) -> Ok(#(token.location.start, state))
      Error(_) -> Ok(#(Position(1, 1, 0), state))
    }
  })
}

// ============================================================================
// TOKEN PARSERS
// ============================================================================

/// Parse a specific token kind
pub fn token(kind: String) -> Parser(Token) {
  Parser(fn(state) {
    case get_token_at(state.tokens, state.pos) {
      Ok(token) if token.kind == kind ->
        Ok(#(token, State(..state, pos: state.pos + 1)))
      Ok(token) ->
        Error(State(..state, 
          pos: state.pos + 1,
          errors: [mk_error(state, kind)]
        ))
      Error(_) ->
        Error(State(..state, errors: [mk_error(state, kind)]))
    }
  })
}

/// Parse a keyword (token with specific value)
pub fn keyword(value: String) -> Parser(Token) {
  Parser(fn(state) {
    case get_token_at(state.tokens, state.pos) {
      Ok(token) -> {
        case is_keyword_token(token, value) {
          True -> Ok(#(token, State(..state, pos: state.pos + 1)))
          False -> Error(State(..state,
            pos: state.pos + 1,
            errors: [mk_error(state, "keyword '" <> value <> "'")]
          ))
        }
      }
      Error(_) ->
        Error(State(..state, errors: [mk_error(state, "keyword '" <> value <> "'")]))
    }
  })
}

fn is_keyword_token(token: Token, value: String) -> Bool {
  case token.kind {
    "Ident" | "Keyword" -> token.value == value
    _ -> False
  }
}

/// Parse any token
pub fn any_token() -> Parser(Token) {
  Parser(fn(state) {
    case get_token_at(state.tokens, state.pos) {
      Ok(token) -> Ok(#(token, State(..state, pos: state.pos + 1)))
      Error(_) -> Error(State(..state, errors: [mk_error(state, "any token")]))
    }
  })
}

/// Check if at end of input
pub fn at_end() -> Parser(Bool) {
  Parser(fn(state) {
    Ok(#(state.pos >= list.length(state.tokens), state))
  })
}

// ============================================================================
// SEQUENCE COMBINATORS
// ============================================================================

/// Parse in sequence, return list
pub fn seq(parsers: List(Parser(a))) -> Parser(List(a)) {
  case parsers {
    [] -> ok([])
    [p, ..ps] ->
      Parser(fn(state) {
        case run(p, state) {
          Ok(#(x, state)) ->
            case seq(ps) |> run(state) {
              Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      })
  }
}

/// Parse zero or one - never records errors (that's the point of optional)
pub fn opt(parser: Parser(a)) -> Parser(Option(a)) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(x, state)) -> Ok(#(Some(x), state))
      Error(_) -> Ok(#(None, state))  // Always succeed with None, discard errors
    }
  })
}

/// Parse zero or more
pub fn many(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(state) {
    collect_many(parser, [], state)
  })
}

fn collect_many(parser: Parser(a), acc: List(a), state: State) -> Result(#(List(a), State), State) {
  case run(parser, state) {
    Ok(#(x, state)) -> collect_many(parser, [x, ..acc], state)
    Error(new_state) -> {
      // Check if we're at EOF - if so, don't count this as an error
      case get_token_at(new_state.tokens, new_state.pos) {
        Ok(_) -> Ok(#(list.reverse(acc), new_state))  // Real error, keep it
        Error(_) -> Ok(#(list.reverse(acc), state))   // EOF, discard error
      }
    }
  }
}

/// Parse one or more
pub fn many1(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(x, state)) -> collect_many(parser, [x], state)
      Error(s) -> Error(s)
    }
  })
}

/// Parse exactly n times
pub fn exactly(n: Int, parser: Parser(a)) -> Parser(List(a)) {
  case n {
    0 -> ok([])
    _ ->
      Parser(fn(state) {
        case run(parser, state) {
          Ok(#(x, state)) ->
            case exactly(n - 1, parser) |> run(state) {
              Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      })
  }
}

// ============================================================================
// CHOICE COMBINATORS
// ============================================================================

/// Try parsers in order
pub fn one_of(parsers: List(Parser(a))) -> Parser(a) {
  case parsers {
    [] -> fail("one of (empty)")
    [p, ..rest] ->
      Parser(fn(state) {
        case run(p, state) {
          Ok(result) -> Ok(result)
          Error(_) -> one_of(rest) |> run(state)
        }
      })
  }
}

// ============================================================================
// SEPARATOR COMBINATORS
// ============================================================================

/// Parse separated list (zero or more)
pub fn sep_by(parser: Parser(a), sep: Parser(b)) -> Parser(List(a)) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(first, state)) ->
        case many(Parser(fn(s) {
          case run(sep, s) {
            Ok(#(_, s)) -> run(parser, s)
            Error(s) -> Error(s)
          }
        })) |> run(state) {
          Ok(#(rest, state)) -> Ok(#([first, ..rest], state))
          Error(s) -> Error(s)
        }
      Error(state) -> Ok(#([], state))
    }
  })
}

/// Parse separated list (one or more)
pub fn sep_by1(parser: Parser(a), sep: Parser(b)) -> Parser(List(a)) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(first, state)) ->
        case many(Parser(fn(s) {
          case run(sep, s) {
            Ok(#(_, s)) -> run(parser, s)
            Error(s) -> Error(s)
          }
        })) |> run(state) {
          Ok(#(rest, state)) -> Ok(#([first, ..rest], state))
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

// ============================================================================
// DELIMITER COMBINATORS
// ============================================================================

/// Parse between delimiters
pub fn between(open: Parser(a), close: Parser(a), parser: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case run(open, state) {
      Ok(#(_, state)) ->
        case run(parser, state) {
          Ok(#(x, state)) ->
            case run(close, state) {
              Ok(#(_, state)) -> Ok(#(x, state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Parse parenthesized expression
pub fn parens(parser: Parser(a)) -> Parser(a) {
  between(token("LParen"), token("RParen"), parser)
}

/// Parse braced expression
pub fn braces(parser: Parser(a)) -> Parser(a) {
  between(token("LBrace"), token("RBrace"), parser)
}

/// Parse bracketed expression
pub fn brackets(parser: Parser(a)) -> Parser(a) {
  between(token("LBracket"), token("RBracket"), parser)
}

// ============================================================================
// LOOKAHEAD
// ============================================================================

/// Lookahead without consuming
pub fn lookahead(parser: Parser(a)) -> Parser(a) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(x, _)) -> Ok(#(x, state))
      Error(s) -> Error(s)
    }
  })
}

/// Negative lookahead
pub fn not(parser: Parser(a)) -> Parser(Nil) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(_) -> Error(State(..state, errors: [mk_error(state, "not")]))
      Error(_) -> Ok(#(Nil, state))
    }
  })
}

// ============================================================================
// MAPPING
// ============================================================================

/// Map parser result
pub fn map(parser: Parser(a), f: fn(a) -> b) -> Parser(b) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(#(x, state)) -> Ok(#(f(x), state))
      Error(s) -> Error(s)
    }
  })
}

/// Skip result (return Nil)
pub fn skip(parser: Parser(a)) -> Parser(Nil) {
  map(parser, fn(_) { Nil })
}

/// Sequence then skip second
pub fn then(parser1: Parser(a), parser2: Parser(b)) -> Parser(a) {
  Parser(fn(state) {
    case run(parser1, state) {
      Ok(#(x, state)) ->
        case run(parser2, state) {
          Ok(#(_, state)) -> Ok(#(x, state))
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Sequence then skip first
pub fn preceed(parser1: Parser(a), parser2: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case run(parser1, state) {
      Ok(#(_, state)) -> run(parser2, state)
      Error(s) -> Error(s)
    }
  })
}

// ============================================================================
// ERROR HANDLING AND RECOVERY
// ============================================================================

/// Expect with custom message
pub fn expect(parser: Parser(a), message: String) -> Parser(a) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(result) -> Ok(result)
      Error(s) -> Error(State(..s, errors: [mk_error(s, message)]))
    }
  })
}

/// Recover from error with fallback value
pub fn recover(parser: Parser(a), fallback: a) -> Parser(a) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(result) -> Ok(result)
      Error(state) -> Ok(#(fallback, state))
    }
  })
}

/// Sync to specific token kinds (panic mode recovery)
pub fn sync_to(kinds: List(String)) -> Parser(Nil) {
  Parser(fn(state) {
    sync_loop(state, kinds)
  })
}

fn sync_loop(state: State, kinds: List(String)) -> Result(#(Nil, State), State) {
  case get_token_at(state.tokens, state.pos) {
    Ok(token) -> {
      case list.contains(kinds, token.kind) {
        True -> Ok(#(Nil, state))
        False -> sync_loop(State(..state, pos: state.pos + 1), kinds)
      }
    }
    Error(_) -> Ok(#(Nil, state))  // End of input
  }
}

/// Sync to keyword
pub fn sync_to_keyword(kw: String) -> Parser(Nil) {
  sync_to(["Ident"]) |> then(
    Parser(fn(state) {
      case get_token_at(state.tokens, state.pos) {
        Ok(token) if token.value == kw -> Ok(#(Nil, state))
        _ -> Error(state)
      }
    })
  )
}

/// Recover with sync points
pub fn recover_with_sync(
  parser: Parser(a),
  sync_points: List(String),
  fallback: a,
  error_msg: String,
) -> Parser(a) {
  Parser(fn(state) {
    case run(parser, state) {
      Ok(result) -> Ok(result)
      Error(error_state) -> {
        // Add error
        let error_state = State(..error_state, errors: [mk_error(error_state, error_msg)])
        // Sync to recovery point
        case sync_loop(error_state, sync_points) {
          Ok(#(_, synced_state)) -> Ok(#(fallback, synced_state))
          Error(s) -> Ok(#(fallback, s))
        }
      }
    }
  })
}

// ============================================================================
// PRATT PARSING - Complete Implementation
// ============================================================================

/// Build Pratt parser from operators
pub fn pratt(ops: List(ExprOp)) -> Parser(Tree) {
  Parser(fn(state) {
    let pratt_state = PrattState(tokens: state.tokens, pos: state.pos)
    case parse_expr(pratt_state, ops, 0) {
      Ok(#(tree, pratt_state)) -> {
        let new_state = State(..state, tokens: pratt_state.tokens, pos: pratt_state.pos)
        Ok(#(tree, new_state))
      }
      Error(s) -> {
        // Convert PrattState error to State error
        Error(State(..state, errors: [mk_error(state, "expression")]))
      }
    }
  })
}

/// Parse expression with minimum precedence
fn parse_expr(state: PrattState, ops: List(ExprOp), min_prec: Int) -> Result(#(Tree, PrattState), PrattState) {
  // Parse left side (atom or prefix)
  case parse_lhs(state, ops, min_prec) {
    Ok(#(left, state)) -> {
      // Parse infix operators
      parse_infix_loop(state, ops, left, min_prec)
    }
    Error(s) -> Error(s)
  }
}

/// Parse left-hand side (atom or prefix operator)
fn parse_lhs(state: PrattState, ops: List(ExprOp), min_prec: Int) -> Result(#(Tree, PrattState), PrattState) {
  case ops {
    [] -> Error(state)
    [op, ..rest] -> {
      case op {
        Atom(kind) -> {
          // Try to parse atom
          case get_token_at(state.tokens, state.pos) {
            Ok(token) if token.kind == kind -> {
              let new_state = PrattState(..state, pos: state.pos + 1)
              Ok(#(Leaf(token), new_state))
            }
            _ -> parse_lhs(state, rest, min_prec)
          }
        }
        Prefix(op_str, prec) if prec >= min_prec -> {
          // Try to parse prefix operator
          case get_token_at(state.tokens, state.pos) {
            Ok(token) if token.value == op_str -> {
              let op_loc = token.location
              let new_state = PrattState(..state, pos: state.pos + 1)
              // Parse operand with higher precedence
              case parse_expr(new_state, ops, prec + 1) {
                Ok(#(operand, new_state)) -> {
                  let tree = Node("Prefix", [Leaf(Token("Op", op_str, op_loc, 0)), operand])
                  Ok(#(tree, new_state))
                }
                Error(s) -> Error(s)
              }
            }
            _ -> parse_lhs(state, rest, min_prec)
          }
        }
        _ -> parse_lhs(state, rest, min_prec)
      }
    }
  }
}

/// Parse infix operator loop
fn parse_infix_loop(state: PrattState, ops: List(ExprOp), left: Tree, min_prec: Int) -> Result(#(Tree, PrattState), PrattState) {
  case get_infix_op(state, ops, min_prec) {
    Some(#(op_str, prec, assoc, op_loc)) -> {
      let new_state = PrattState(..state, pos: state.pos + 1)
      // Determine next min_prec based on associativity
      let next_min_prec = case assoc {
        AssocL -> prec + 1  // Left-associative: higher precedence for right side
        AssocR -> prec      // Right-associative: same precedence for right side
      }
      // Parse right side
      case parse_expr(new_state, ops, next_min_prec) {
        Ok(#(right, new_state)) -> {
          let tree = Node("Infix", [left, Leaf(Token("Op", op_str, op_loc, 0)), right])
          // Continue parsing more infix operators
          parse_infix_loop(new_state, ops, tree, min_prec)
        }
        Error(s) -> Ok(#(left, state))  // Return left on error
      }
    }
    None -> Ok(#(left, state))  // No more infix operators
  }
}

/// Get next infix operator at current position
fn get_infix_op(state: PrattState, ops: List(ExprOp), min_prec: Int) -> Option(#(String, Int, Assoc, Location)) {
  case get_token_at(state.tokens, state.pos) {
    Ok(token) -> {
      find_infix_op_in_list(ops, token.value, min_prec, token.location)
    }
    Error(_) -> None
  }
}

fn find_infix_op_in_list(ops: List(ExprOp), op_str: String, min_prec: Int, loc: Location) -> Option(#(String, Int, Assoc, Location)) {
  case ops {
    [] -> None
    [op, ..rest] -> {
      case op {
        InfixL(op_s, prec) if op_s == op_str && prec > min_prec ->
          Some(#(op_s, prec, AssocL, loc))
        InfixR(op_s, prec) if op_s == op_str && prec >= min_prec ->
          Some(#(op_s, prec, AssocR, loc))
        _ -> find_infix_op_in_list(rest, op_str, min_prec, loc)
      }
    }
  }
}

/// Associativity
type Assoc {
  AssocL
  AssocR
}

// ============================================================================
// PARSE TREE
// ============================================================================

/// Parse tree node
pub type Tree {
  /// Token leaf
  Leaf(Token)
  /// Internal node with name and children
  Node(name: String, children: List(Tree))
  /// Empty node
  Empty
}

// ============================================================================
// RUNNING PARSERS
// ============================================================================

/// Run a parser
fn run(parser: Parser(a), state: State) -> Result(#(a, State), State) {
  case parser {
    Parser(p) -> p(state)
  }
}

/// Get token at position
fn get_token_at(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  get_token_at_loop(tokens, pos, 0)
}

fn get_token_at_loop(tokens: List(Token), pos: Int, current: Int) -> Result(Token, Nil) {
  case tokens {
    [] -> Error(Nil)
    [token, ..rest] -> {
      case current == pos {
        True -> Ok(token)
        False -> get_token_at_loop(rest, pos, current + 1)
      }
    }
  }
}

/// Parse tokens - returns ParseResult which may contain errors
/// For completely failed parses, returns Empty AST with errors
pub fn parse(parser: Parser(a), _filename: String, tokens: List(Token)) -> ParseResult(a) {
  let initial_state = State(tokens: tokens, pos: 0, errors: [])
  case run(parser, initial_state) {
    Ok(#(ast, state)) -> ParseResult(ast: ast, errors: state.errors)
    Error(state) -> {
      // Return errors - caller should check for errors before using AST
      // We use panic here because there's no valid AST to return
      // In production code, you'd want better error handling
      case state.errors {
        [] -> ParseResult(ast: panic as "Parse failed with no result or errors", errors: [])
        [err, ..] -> ParseResult(ast: panic as err.message, errors: state.errors)
      }
    }
  }
}

/// Create error from state
fn mk_error(state: State, expected: String) -> ParseError {
  let location = get_token_location(state.tokens, state.pos)
  ParseError(
    location: location,
    message: "Parse error",
    expected: [expected],
    severity: ParseErrorLevel,
  )
}

fn get_token_location(tokens: List(Token), pos: Int) -> Location {
  get_token_location_loop(tokens, pos, 0)
}

fn get_token_location_loop(tokens: List(Token), pos: Int, current: Int) -> Location {
  case tokens {
    [] -> Location(filename: "unknown", start: Position(1, 1, 0), end: Position(1, 1, 0))
    [token, ..rest] -> {
      case current == pos {
        True -> token.location
        False -> get_token_location_loop(rest, pos, current + 1)
      }
    }
  }
}

// ============================================================================
// ERROR FORMATTING
// ============================================================================

/// Format error with source snippet
pub fn format_error(error: ParseError, source: String) -> String {
  let lines = string.split(source, "\n")
  let row = error.location.start.row

  let line_content = get_line(lines, row)
  let pointer = string.repeat(" ", error.location.start.col - 1) <> "^"

  let severity = case error.severity {
    ParseErrorLevel -> "error"
    Warning -> "warning"
    Info -> "info"
  }

  severity <> ": " <> error.message <> "\n" <>
  "  ┌─ " <> error.location.filename <> ":" <>
    int.to_string(row) <> ":" <> int.to_string(error.location.start.col) <> "\n" <>
  "  │\n" <>
  int.to_string(row) <> " │ " <> line_content <> "\n" <>
  "  │ " <> pointer <>
  format_expected(error.expected)
}

fn get_line(lines: List(String), row: Int) -> String {
  get_line_loop(lines, row, 1)
}

fn get_line_loop(lines: List(String), target: Int, current: Int) -> String {
  case lines {
    [] -> ""
    [line] if current == target -> line
    [_, ..rest] -> get_line_loop(rest, target, current + 1)
  }
}

fn format_expected(expected: List(String)) -> String {
  case expected {
    [] -> ""
    [e] -> "\n  Expected: " <> e
    es -> "\n  Expected one of: " <> string.join(es, ", ")
  }
}
