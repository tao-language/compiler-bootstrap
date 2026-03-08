// ============================================================================
// GRAMMAR - Simple Grammar DSL with Direct AST Construction
// ============================================================================
/// A simple grammar DSL where each rule directly constructs the AST.
///
/// # Example
///
/// ```gleam
/// import grammar
/// import calc/ast
///
/// let g = grammar.new()
///   |> grammar.start("Expr")
///   |> grammar.rule(
///     "Add",
///     fn(g) {
///       parser.map(parser.seq([
///         grammar.parse_ref(g, "Term"),
///         grammar.parse_token(g, "Plus"),
///         grammar.parse_ref(g, "Expr"),
///       ]), fn([left, _plus, right]) {
///         ast.Expr.Add(left, right)
///       })
///     },
///   )
/// ```
import gleam/dict.{type Dict}
import gleam/list
import gleam/result
import lexer
import parser.{type ParseResult, type Token}

// ============================================================================
// TYPES
// ============================================================================

/// Generic grammar parameterized by AST type
pub type Grammar(ast) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(ast)),
    tokens: List(String),
    keywords: List(String),
  )
}

type Rule(ast) =
  fn(Grammar(ast)) -> Parser(ast)

pub type Parser(a) {
  Parser(fn(ParserState) -> ParseResultInternal(a))
}

pub type ParserState {
  ParserState(tokens: List(Token), pos: Int)
}

pub type ParseResultInternal(a) {
  ParseOk(ast: a, pos: Int)
  ParseError
}

// ============================================================================
// GRAMMAR CONSTRUCTION
// ============================================================================

/// Create new empty grammar
pub fn new() -> Grammar(a) {
  Grammar(
    name: "Grammar",
    start: "Start",
    rules: dict.new(),
    tokens: [],
    keywords: [],
  )
}

/// Set start rule
pub fn start(g: Grammar(a), rule: String) -> Grammar(a) {
  Grammar(..g, start: rule)
}

/// Add token kind
pub fn with_token(g: Grammar(a), kind: String) -> Grammar(a) {
  Grammar(..g, tokens: [kind, ..g.tokens])
}

/// Add keyword
pub fn with_keyword(g: Grammar(a), kw: String) -> Grammar(a) {
  Grammar(..g, keywords: [kw, ..g.keywords])
}

/// Add rule with parser function
pub fn rule(
  g: Grammar(a),
  name: String,
  make_parser: fn(Grammar(a)) -> Parser(a),
) -> Grammar(a) {
  let rules = dict.insert(g.rules, name, make_parser)
  Grammar(..g, rules: rules)
}

// ============================================================================
// PARSER HELPERS
// ============================================================================

/// Parse a token by kind
pub fn parse_token(g: Grammar(a), kind: String) -> Parser(Token) {
  Parser(fn(state) {
    case get_token(state.tokens, state.pos) {
      Ok(token) if token.kind == kind -> {
        ParseOk(ast: token, pos: state.pos + 1)
      }
      _ -> ParseError
    }
  })
}

/// Parse a keyword
pub fn parse_keyword(g: Grammar(a), kw: String) -> Parser(Token) {
  Parser(fn(state) {
    case get_token(state.tokens, state.pos) {
      Ok(token) if token.kind == "Ident" && token.value == kw -> {
        ParseOk(ast: token, pos: state.pos + 1)
      }
      _ -> ParseError
    }
  })
}

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  get_token_loop(tokens, pos, 0)
}

fn get_token_loop(tokens: List(Token), pos: Int, current: Int) -> Result(Token, Nil) {
  case tokens {
    [] -> Error(Nil)
    [token, ..rest] -> {
      case current == pos {
        True -> Ok(token)
        False -> get_token_loop(rest, pos, current + 1)
      }
    }
  }
}

/// Parse a reference to another rule
pub fn parse_ref(g: Grammar(a), name: String) -> Parser(a) {
  case dict.get(g.rules, name) {
    Ok(rule_maker) -> rule_maker(g)
    Error(_) -> Parser(fn(_) { ParseError })
  }
}

// ============================================================================
// PARSER COMBINATORS
// ============================================================================

/// Map parser result
pub fn map(p: Parser(a), f: fn(a) -> b) -> Parser(b) {
  Parser(fn(state) {
    case run_parser(p, state) {
      ParseOk(ast, pos) -> ParseOk(ast: f(ast), pos: pos)
      ParseError -> ParseError
    }
  })
}

/// Sequence of parsers
pub fn seq(parsers: List(Parser(a))) -> Parser(List(a)) {
  Parser(fn(state) {
    seq_loop(parsers, state, [])
  })
}

fn seq_loop(parsers: List(Parser(a)), state: ParserState, acc: List(a)) -> ParseResultInternal(List(a)) {
  case parsers {
    [] -> ParseOk(ast: list.reverse(acc), pos: state.pos)
    [p, ..rest] -> {
      case run_parser(p, state) {
        ParseOk(result, new_pos) -> seq_loop(rest, ParserState(..state, pos: new_pos), [result, ..acc])
        ParseError -> ParseError
      }
    }
  }
}

/// Choice of parsers
pub fn choice(parsers: List(Parser(a))) -> Parser(a) {
  Parser(fn(state) {
    choice_loop(parsers, state)
  })
}

fn choice_loop(parsers: List(Parser(a)), state: ParserState) -> ParseResultInternal(a) {
  case parsers {
    [] -> ParseError
    [p, ..rest] -> {
      case run_parser(p, state) {
        ParseOk(_, _) as result -> result
        ParseError -> choice_loop(rest, state)
      }
    }
  }
}

fn run_parser(p: Parser(a), state: ParserState) -> ParseResultInternal(a) {
  case p {
    Parser(f) -> f(state)
  }
}

// ============================================================================
// PARSING
// ============================================================================

/// Parse source using grammar
pub fn parse(g: Grammar(a), source: String) -> ParseResult(a) {
  let tokens = lexer.tokenize(lexer.default_config(), g.name, source)
  let state = ParserState(tokens: tokens, pos: 0)

  // Get start rule parser
  case dict.get(g.rules, g.start) {
    Ok(rule_maker) -> {
      let rule_parser = rule_maker(g)
      case run_parser(rule_parser, state) {
        ParseOk(ast, _) -> parser.ParseResult(ast: ast, errors: [])
        ParseError -> parser.ParseResult(ast: panic as "Parse failed", errors: [])
      }
    }
    Error(_) -> {
      parser.ParseResult(ast: panic as "No start rule", errors: [])
    }
  }
}
