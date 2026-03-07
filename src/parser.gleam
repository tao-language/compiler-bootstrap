// ============================================================================
// PARSER - Generic Parser Combinator Library with Error Recovery
// ============================================================================
/// A generic parser combinator library for parsing any programming language.

import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// Source position in the source file
pub type Position {
  Position(row: Int, col: Int)
}

/// Source location with filename and range
pub type Location {
  Location(filename: String, range: Range)
}

/// Range of positions
pub type Range {
  Range(start: Position, end: Position)
}

/// Error severity
pub type ErrorSeverity {
  ParseErrorLevel
  Warning
  Info
}

/// Parse error with location and message
pub type ParseError {
  ParseError(
    location: Location,
    message: String,
    expected: List(String),
    severity: ErrorSeverity,
  )
}

/// Parser result - always succeeds with AST and errors
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}

/// Parser state with remaining input and location tracking
pub type State {
  State(
    remaining: String,
    filename: String,
    pos: Position,
    index: Int,
    expected: String,
    committed: String,
  )
}

/// A parser that produces a value of type `a`
pub type Parser(a) {
  Parser(fn(State) -> Result(#(a, State), State))
}

// ============================================================================
// CORE PARSERS
// ============================================================================

/// Parser that succeeds with a value
pub fn ok(a: a) -> Parser(a) {
  Parser(fn(state) { Ok(#(a, state)) })
}

/// Parser that always fails
pub fn fail() -> Parser(a) {
  Parser(fn(state) { Error(state) })
}

/// Get current state
pub fn get_state() -> Parser(State) {
  Parser(fn(state) { Ok(#(state, state)) })
}

/// Get current position
pub fn position() -> Parser(Position) {
  Parser(fn(state) { Ok(#(state.pos, state)) })
}

// ============================================================================
// CHARACTER PARSERS
// ============================================================================

/// Parse any character
pub fn any_char() -> Parser(String) {
  Parser(fn(state) {
    case string.pop_grapheme(state.remaining) {
      Error(Nil) -> Error(state)
      Ok(#(char, rest)) ->
        Ok(#(
          char,
          State(
            remaining: rest,
            filename: state.filename,
            pos: case char {
              "\n" -> Position(state.pos.row + 1, 1)
              _ -> Position(state.pos.row, state.pos.col + 1)
            },
            index: state.index + 1,
            expected: state.expected,
            committed: state.committed,
          ),
        ))
    }
  })
}

/// Parse a specific character
pub fn char(c: String) -> Parser(String) {
  expect("character '" <> c <> "'", char_if(fn(c2) { c == c2 }))
}

/// Parse a character satisfying a predicate
pub fn char_if(pred: fn(String) -> Bool) -> Parser(String) {
  if_(pred, any_char())
}

/// Parse one of several characters
pub fn char_of(chars: List(String)) -> Parser(String) {
  expect("one of " <> string.join(chars, ", "), char_if(fn(c) { list.contains(chars, c) }))
}

/// Parse a letter
pub fn letter() -> Parser(String) {
  expect("letter", char_if(is_letter))
}

/// Parse a digit
pub fn digit() -> Parser(String) {
  expect("digit", char_if(is_digit))
}

/// Parse a letter or digit
pub fn alphanumeric() -> Parser(String) {
  expect("letter or digit", char_if(is_alphanumeric))
}

/// Parse whitespace (space or tab)
pub fn space() -> Parser(String) {
  char_of([" ", "\t"])
}

/// Parse zero or more whitespace
pub fn spaces() -> Parser(List(String)) {
  zero_or_more(space())
}

/// Parse whitespace including newlines
pub fn whitespace() -> Parser(String) {
  char_of([" ", "\t", "\n", "\r"])
}

/// Parse zero or more whitespace including newlines
pub fn whitespaces() -> Parser(List(String)) {
  zero_or_more(whitespace())
}

// ============================================================================
// TEXT PARSERS
// ============================================================================

/// Parse specific text
pub fn text(str: String) -> Parser(String) {
  let chars = string.to_graphemes(str)
  expect("text '" <> str <> "'", chain(list.map(chars, char)))
  |> map(string.concat)
}

/// Parse one of several texts
pub fn text_of(texts: List(String)) -> Parser(String) {
  one_of(list.map(texts, text))
}

/// Parse a word (alphanumeric sequence)
pub fn word() -> Parser(String) {
  one_or_more(alphanumeric())
  |> map(string.concat)
}

// ============================================================================
// SEQUENCE COMBINATORS
// ============================================================================

/// Chain parsers in sequence
pub fn chain(parsers: List(Parser(a))) -> Parser(List(a)) {
  case parsers {
    [] -> ok([])
    [p, ..ps] ->
      Parser(fn(state) {
        case p |> run(state) {
          Ok(#(x, state)) ->
            case chain(ps) |> run(state) {
              Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      })
  }
}

/// Parse zero or one
pub fn zero_or_one(parser: Parser(a)) -> Parser(Option(a)) {
  one_of([parser |> map(Some), ok(None)])
}

/// Parse zero or more
pub fn zero_or_more(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(state) {
    case one_of([parser |> map(Some), ok(None)]) |> run(state) {
      Ok(#(Some(x), state)) ->
        case zero_or_more(parser) |> run(state) {
          Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
          Error(s) -> Error(s)
        }
      Ok(#(None, state)) -> Ok(#([], state))
      Error(s) -> Error(s)
    }
  })
}

/// Parse one or more
pub fn one_or_more(parser: Parser(a)) -> Parser(List(a)) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) ->
        case zero_or_more(parser) |> run(state) {
          Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Parse exactly n times
pub fn exactly(n: Int, parser: Parser(a)) -> Parser(List(a)) {
  chain(list.repeat(parser, n))
}

/// Parse at least n times
pub fn at_least(n: Int, parser: Parser(a)) -> Parser(List(a)) {
  case n <= 0 {
    True -> zero_or_more(parser)
    False ->
      Parser(fn(state) {
        case parser |> run(state) {
          Ok(#(x, state)) ->
            case at_least(n - 1, parser) |> run(state) {
              Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      })
  }
}

/// Parse at most n times
pub fn at_most(n: Int, parser: Parser(a)) -> Parser(List(a)) {
  case n <= 0 {
    True -> ok([])
    False ->
      one_of([
        Parser(fn(state) {
          case parser |> run(state) {
            Ok(#(x, state)) ->
              case at_most(n - 1, parser) |> run(state) {
                Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
                Error(s) -> Error(s)
              }
            Error(s) -> Error(s)
          }
        }),
        ok([]),
      ])
  }
}

/// Parse between min and max times
pub fn between(min: Int, max: Int, parser: Parser(a)) -> Parser(List(a)) {
  case min <= 0 {
    True -> at_most(max, parser)
    False -> at_least(min, parser)
  }
}

// ============================================================================
// CHOICE COMBINATORS
// ============================================================================

/// Try parsers in order, return first success
pub fn one_of(parsers: List(Parser(a))) -> Parser(a) {
  case parsers {
    [] -> fail()
    [p, ..choices] ->
      Parser(fn(s1) {
        case p |> run(s1) {
          Ok(result) -> Ok(result)
          Error(_) -> one_of(choices) |> run(s1)
        }
      })
  }
}

/// Commit to first successful parse
pub fn commit_one_of(parsers: List(Parser(a))) -> Parser(a) {
  case parsers {
    [] -> fail()
    [p, ..choices] ->
      Parser(fn(s1) {
        case p |> run(State(..s1, committed: "")) {
          Ok(#(x, s2)) -> Ok(#(x, State(..s2, committed: s1.committed)))
          Error(s2) if s2.committed == "" -> commit_one_of(choices) |> run(s1)
          Error(s2) -> Error(State(..s1, expected: s2.expected))
        }
      })
  }
}

// ============================================================================
// PADDING AND DELIMITERS
// ============================================================================

/// Pad parser on the left
pub fn padded_l(padding: Parser(a), parser: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case padding |> run(state) {
      Ok(#(_, state)) -> parser |> run(state)
      Error(s) -> Error(s)
    }
  })
}

/// Pad parser on the right
pub fn padded_r(padding: Parser(a), parser: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) ->
        case padding |> run(state) {
          Ok(#(_, state)) -> Ok(#(x, state))
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Pad parser on both sides
pub fn padded(padding: Parser(a), parser: Parser(b)) -> Parser(b) {
  padded_l(padding, padded_r(padding, parser))
}

/// Parse between delimiters
pub fn inbetween(start: Parser(a), end: Parser(a), parser: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case start |> run(state) {
      Ok(#(_, state)) ->
        case parser |> run(state) {
          Ok(#(x, state)) ->
            case end |> run(state) {
              Ok(#(_, state)) -> Ok(#(x, state))
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Parse delimited by open and close
pub fn delimited_by(open: Parser(a), close: Parser(a), parser: Parser(b)) -> Parser(b) {
  inbetween(open, close, parser)
}

/// Parse separated by delimiter
pub fn separated_by(sep: Parser(a), parser: Parser(b)) -> Parser(List(b)) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(first, state)) ->
        case zero_or_more(Parser(fn(s) {
          case sep |> run(s) {
            Ok(#(_, s)) -> parser |> run(s)
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
// LOOKAHEAD AND ASSERTIONS
// ============================================================================

/// Lookahead without consuming
pub fn lookahead(parser: Parser(a)) -> Parser(a) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, _)) -> Ok(#(x, state))
      Error(_) -> Error(state)
    }
  })
}

/// Negative lookahead
pub fn lookahead_not(parser: Parser(a)) -> Parser(Nil) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(_) -> Error(state)
      Error(_) -> Ok(#(Nil, state))
    }
  })
}

/// Assert a condition
pub fn assert_(pred: fn(a) -> Bool, parser: Parser(a)) -> Parser(a) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) ->
        case pred(x) {
          True -> Ok(#(x, state))
          False -> Error(state)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Negate a parser
pub fn not(parser: Parser(a)) -> Parser(Nil) {
  lookahead_not(parser)
}

// ============================================================================
// ERROR HANDLING
// ============================================================================

/// Expect a specific message on failure
pub fn expect(message: String, parser: Parser(a)) -> Parser(a) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(result) -> Ok(result)
      Error(s) -> Error(State(..s, expected: message))
    }
  })
}

/// Sync to a synchronization point
pub fn sync_to(sync_points: List(Parser(a))) -> Parser(Nil) {
  Parser(fn(state) {
    case one_of(sync_points) |> run(state) {
      Ok(#(_, state)) -> Ok(#(Nil, state))
      Error(state) ->
        case string.pop_grapheme(state.remaining) {
          Error(Nil) -> Error(state)
          Ok(#(_, rest)) -> sync_to(sync_points) |> run(State(..state, remaining: rest))
        }
    }
  })
}

/// Skip until end of line
pub fn sync_to_eol() -> Parser(Nil) {
  sync_to([char("\n") |> skip, end_of_file()])
}

/// Skip current token
pub fn skip_token() -> Parser(Nil) {
  Parser(fn(state) {
    case string.pop_grapheme(state.remaining) {
      Error(Nil) -> Error(state)
      Ok(#(_, rest)) -> Ok(#(Nil, State(..state, remaining: rest)))
    }
  })
}

// ============================================================================
// EXPRESSION PARSERS (PRATT PARSING)
// ============================================================================

/// Expression parser type for Pratt parsing
pub type ExprParser(a) {
  Atom(fn(Parser(a)) -> Parser(a))
  Prefix(Int, fn(Parser(a)) -> Parser(a))
  InfixL(Int, fn(a, Parser(a)) -> Parser(a))
  InfixR(Int, fn(a, Parser(a)) -> Parser(a))
}

/// Atom parser
pub fn atom(_f: fn(a) -> b, parser: Parser(a)) -> ExprParser(a) {
  Atom(fn(_expr) { parser })
}

/// Prefix operator
pub fn prefix(
  precedence: Int,
  f: fn(Location, op, a) -> a,
  spaces: Parser(List(String)),
  op: Parser(op),
) -> ExprParser(a) {
  Prefix(precedence, fn(expr) {
    Parser(fn(state) {
      case position() |> run(state) {
        Ok(#(op_loc, state)) ->
          case op |> run(state) {
            Ok(#(op_val, state)) ->
              case spaces |> run(state) {
                Ok(#(_, state)) ->
                  case expr |> run(state) {
                    Ok(#(x, state)) ->
                      Ok(#(f(Location(state.filename, Range(op_loc, state.pos)), op_val, x), state))
                    Error(s) -> Error(s)
                  }
                Error(s) -> Error(s)
              }
            Error(s) -> Error(s)
          }
        Error(s) -> Error(s)
      }
    })
  })
}

/// Left-associative infix operator
pub fn infix_l(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(List(String)),
  op: Parser(op),
) -> ExprParser(a) {
  InfixL(precedence, fn(x, expr) {
    Parser(fn(state) {
      case position() |> run(state) {
        Ok(#(op_loc, state)) ->
          case op |> run(state) {
            Ok(#(op_val, state)) ->
              case spaces |> run(state) {
                Ok(#(_, state)) ->
                  case expr |> run(state) {
                    Ok(#(y, state)) ->
                      Ok(#(f(Location(state.filename, Range(op_loc, state.pos)), op_val, x, y), state))
                    Error(s) -> Error(s)
                  }
                Error(s) -> Error(s)
              }
            Error(s) -> Error(s)
          }
        Error(s) -> Error(s)
      }
    })
  })
}

/// Right-associative infix operator
pub fn infix_r(
  precedence: Int,
  f: fn(Location, op, a, a) -> a,
  spaces: Parser(List(String)),
  op: Parser(op),
) -> ExprParser(a) {
  InfixR(precedence, fn(x, expr) {
    Parser(fn(state) {
      case position() |> run(state) {
        Ok(#(op_loc, state)) ->
          case op |> run(state) {
            Ok(#(op_val, state)) ->
              case spaces |> run(state) {
                Ok(#(_, state)) ->
                  case expr |> run(state) {
                    Ok(#(y, state)) ->
                      Ok(#(f(Location(state.filename, Range(op_loc, state.pos)), op_val, x, y), state))
                    Error(s) -> Error(s)
                  }
                Error(s) -> Error(s)
              }
            Error(s) -> Error(s)
          }
        Error(s) -> Error(s)
      }
    })
  })
}

/// Build expression parser with precedence
pub fn precedence(ops: List(ExprParser(a)), min_prec: Int) -> Parser(a) {
  case ops {
    [] -> fail()
    _ ->
      Parser(fn(state) {
        case parse_atom_or_prefix(ops, min_prec, state) {
          Ok(#(x, state)) -> parse_infix_loop(ops, min_prec, x, state)
          Error(s) -> Error(s)
        }
      })
  }
}

fn parse_atom_or_prefix(
  ops: List(ExprParser(a)),
  min_prec: Int,
  state: State,
) -> Result(#(a, State), State) {
  case ops {
    [] -> Error(state)
    [Atom(op), ..rest] ->
      op(fail()) |> run(state)
    [Prefix(prec, op), ..rest] if prec >= min_prec ->
      op(fail()) |> run(state)
    [_, ..rest] -> parse_atom_or_prefix(rest, min_prec, state)
  }
}

fn parse_infix_loop(
  ops: List(ExprParser(a)),
  min_prec: Int,
  x: a,
  state: State,
) -> Result(#(a, State), State) {
  // Simplified: just return the atom value without infix parsing
  Ok(#(x, state))
}

fn get_infix_op(
  ops: List(ExprParser(a)),
  min_prec: Int,
) -> Option(#(Int, fn(a, Parser(a)) -> Parser(a))) {
  case ops {
    [] -> None
    [InfixL(prec, op), ..] if prec > min_prec -> Some(#(prec, op))
    [InfixR(prec, op), ..] if prec >= min_prec -> Some(#(prec, op))
    [_, ..rest] -> get_infix_op(rest, min_prec)
  }
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Run a parser
fn run(parser: Parser(a), state: State) -> Result(#(a, State), State) {
  case parser {
    Parser(p) -> p(state)
  }
}

/// Parse with a state
pub fn parse(parser: Parser(a), filename: String, source: String) -> Result(#(a, State), State) {
  let initial_state = State(
    remaining: source,
    filename: filename,
    pos: Position(1, 1),
    index: 0,
    expected: "",
    committed: "",
  )
  run(parser, initial_state)
}

/// Map parser result
pub fn map(parser: Parser(a), f: fn(a) -> b) -> Parser(b) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) -> Ok(#(f(x), state))
      Error(s) -> Error(s)
    }
  })
}

/// Skip parser result
pub fn skip(parser: Parser(a)) -> Parser(Nil) {
  parser |> map(fn(_) { Nil })
}

/// Skip then parse
pub fn skip_then(skip: Parser(a), parser: Parser(b)) -> Parser(b) {
  Parser(fn(state) {
    case skip |> run(state) {
      Ok(#(_, state)) -> parser |> run(state)
      Error(s) -> Error(s)
    }
  })
}

/// Parse then skip
pub fn then_skip(parser: Parser(a), skip: Parser(b)) -> Parser(a) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) ->
        case skip |> run(state) {
          Ok(#(_, state)) -> Ok(#(x, state))
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Until parser
pub fn until(stop: Parser(a), parser: Parser(b)) -> Parser(List(b)) {
  one_of([
    lookahead(stop) |> map(fn(_) { [] }),
    Parser(fn(state) {
      case parser |> run(state) {
        Ok(#(x, state)) ->
          case until(stop, parser) |> run(state) {
            Ok(#(xs, state)) -> Ok(#([x, ..xs], state))
            Error(s) -> Error(s)
          }
        Error(s) -> Error(s)
      }
    }),
  ])
}

/// Text until parser
pub fn text_until(stop: Parser(a)) -> Parser(String) {
  until(stop, any_char()) |> map(string.concat)
}

/// While parser
pub fn while_(cond: fn(a) -> Bool, parser: Parser(a)) -> Parser(List(a)) {
  until(not(if_(cond, parser)), parser)
}

/// Text while parser
pub fn text_while(cond: fn(String) -> Bool) -> Parser(String) {
  while_(cond, any_char()) |> map(string.concat)
}

/// End of file parser
pub fn end_of_file() -> Parser(Nil) {
  Parser(fn(state) {
    case string.is_empty(state.remaining) {
      True -> Ok(#(Nil, state))
      False -> Error(state)
    }
  })
}

/// End of line parser
pub fn end_of_line() -> Parser(Nil) {
  one_of([char("\n") |> skip, end_of_file()])
}

/// Integer parser
pub fn integer() -> Parser(Int) {
  Parser(fn(state) {
    case one_of([char("-") |> map(fn(_) { -1 }), ok(1)]) |> run(state) {
      Ok(#(sign, state)) ->
        case spaces() |> run(state) {
          Ok(#(_, state)) ->
            case one_or_more(digit()) |> run(state) {
              Ok(#(digits, state)) ->
                case lookahead(any_char()) |> run(state) {
                  Ok(#(next, _)) ->
                    case is_digit(next) {
                      True -> Error(state)
                      False ->
                        case int.parse(string.concat(digits)) {
                          Ok(n) -> Ok(#(n * sign, state))
                          Error(_) -> Error(state)
                        }
                    }
                  Error(s) -> Error(s)
                }
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// Float/number parser
pub fn number() -> Parser(Float) {
  Parser(fn(state) {
    case one_of([char("-") |> map(fn(_) { -1.0 }), ok(1.0)]) |> run(state) {
      Ok(#(sign, state)) ->
        case spaces() |> run(state) {
          Ok(#(_, state)) ->
            case one_or_more(digit()) |> run(state) {
              Ok(#(int_digits, state)) ->
                case one_of([
                  Parser(fn(s) {
                    case char(".") |> run(s) {
                      Ok(#(_, s)) ->
                        case one_or_more(digit()) |> run(s) {
                          Ok(#(frac, s)) ->
                            Ok(#(string.concat(int_digits) <> "." <> string.concat(frac), s))
                          Error(s) -> Error(s)
                        }
                      Error(s) -> Error(s)
                    }
                  }),
                  ok(string.concat(int_digits)),
                ]) |> run(state) {
                  Ok(#(num, state)) ->
                    case float.parse(num) {
                      Ok(n) -> Ok(#(n *. sign, state))
                      Error(_) -> Error(state)
                    }
                  Error(s) -> Error(s)
                }
              Error(s) -> Error(s)
            }
          Error(s) -> Error(s)
        }
      Error(s) -> Error(s)
    }
  })
}

/// If parser - conditional parsing
pub fn if_(pred: fn(a) -> Bool, parser: Parser(a)) -> Parser(a) {
  Parser(fn(state) {
    case parser |> run(state) {
      Ok(#(x, state)) ->
        case pred(x) {
          True -> Ok(#(x, state))
          False -> Error(state)
        }
      Error(s) -> Error(s)
    }
  })
}

// ============================================================================
// HELPER FUNCTIONS FOR CHARACTER CLASSIFICATION
// ============================================================================

fn is_letter(c: String) -> Bool {
  case c {
    "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" |
    "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z" |
    "A" | "B" | "C" | "D" | "E" | "F" | "G" | "H" | "I" | "J" | "K" | "L" | "M" |
    "N" | "O" | "P" | "Q" | "R" | "S" | "T" | "U" | "V" | "W" | "X" | "Y" | "Z" -> True
    _ -> False
  }
}

fn is_digit(c: String) -> Bool {
  case c {
    "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" -> True
    _ -> False
  }
}

fn is_alphanumeric(c: String) -> Bool {
  is_letter(c) || is_digit(c)
}
