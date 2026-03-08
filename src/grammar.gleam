// ============================================================================
// GRAMMAR - Generic Grammar DSL with Parser Generation
// ============================================================================
/// A generic grammar DSL that generates parsers for any AST type.
///
/// # Example
///
/// ```gleam
/// import grammar
/// import calc/ast
///
/// let g = grammar.new()
///   |> grammar.start("Expr")
///   |> grammar.rule("Add",
///       grammar.seq([grammar.ref("Term"), grammar.token("Plus"), grammar.ref("Expr")]),
///       fn(children) { ast.Add(left, right) },
///       10,  // Precedence
///   )
///
/// let result = grammar.parse(g, "1 + 2")
/// ```
import gleam/dict.{type Dict}
import gleam/list
import lexer
import parser.{ParseResult, type ParseResult as ParseResultType, type Token}

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

/// Grammar rule with constructor and precedence
pub type Rule(ast) {
  Rule(
    name: String,
    definition: Symbol,
    constructor: fn(List(ParseChild(ast))) -> ast,
    precedence: Int,
  )
}

/// Child of a parse result - either a token or nested AST
/// We use a simple tagged union - the actual AST value is extracted by the constructor
pub type ParseChild(ast) {
  ChildToken(Token)
  ChildAST(ast)
}

/// Grammar symbol (not generic - just describes structure)
pub type Symbol {
  Token(kind: String)
  Keyword(value: String)
  Ref(rule: String)
  Seq(symbols: List(Symbol))
  Choice(alts: List(Symbol))
  Opt(symbol: Symbol)
  Many(symbol: Symbol)
  Sep(item: Symbol, sep: Symbol)
  Sep1(item: Symbol, sep: Symbol)
}

// Internal parse result
type InternalResult(a) {
  InternalResult(children: List(ParseChild(a)), pos: Int)
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

/// Add rule with constructor and precedence
pub fn rule(
  g: Grammar(a),
  name: String,
  definition: Symbol,
  constructor: fn(List(ParseChild(a))) -> a,
  precedence: Int,
) -> Grammar(a) {
  let rule = Rule(name: name, definition: definition, constructor: constructor, precedence: precedence)
  let rules = dict.insert(g.rules, name, rule)
  Grammar(..g, rules: rules)
}

// ============================================================================
// SYMBOL CONSTRUCTORS
// ============================================================================

pub fn token(kind: String) -> Symbol {
  Token(kind)
}

pub fn keyword(value: String) -> Symbol {
  Keyword(value)
}

pub fn ref(name: String) -> Symbol {
  Ref(name)
}

pub fn seq(symbols: List(Symbol)) -> Symbol {
  Seq(symbols)
}

pub fn choice(alts: List(Symbol)) -> Symbol {
  Choice(alts)
}

pub fn opt(symbol: Symbol) -> Symbol {
  Opt(symbol)
}

pub fn many(symbol: Symbol) -> Symbol {
  Many(symbol)
}

pub fn sep(item: Symbol, sep: Symbol) -> Symbol {
  Sep(item, sep)
}

pub fn sep1(item: Symbol, sep: Symbol) -> Symbol {
  Sep1(item, sep)
}

// ============================================================================
// PARSER
// ============================================================================

/// Parse source using grammar
pub fn parse(g: Grammar(a), source: String) -> ParseResultType(a) {
  let tokens = lexer.tokenize(lexer.default_config(), g.name, source)
  
  case dict.get(g.rules, g.start) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, 0) {
        Ok(result) -> {
          let ast = rule.constructor(result.children)
          ParseResult(ast: ast, errors: [])
        }
        Error(_) -> ParseResult(ast: panic as "Parse failed", errors: [])
      }
    }
    Error(_) -> ParseResult(ast: panic as "No start rule", errors: [])
  }
}

fn parse_symbol(
  g: Grammar(a),
  symbol: Symbol,
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case symbol {
    Token(kind) -> parse_token_kind(tokens, pos, kind)
    Keyword(value) -> parse_keyword_value(tokens, pos, value)
    Ref(name) -> parse_ref(g, name, tokens, pos)
    Seq(symbols) -> parse_seq(g, symbols, tokens, pos, [])
    Choice(alts) -> parse_choice(g, alts, tokens, pos)
    Opt(sym) -> parse_opt(g, sym, tokens, pos)
    Many(sym) -> parse_many(g, sym, tokens, pos, [])
    Sep(item, sep) -> parse_sep(g, item, sep, tokens, pos, [])
    Sep1(item, sep) -> parse_sep1(g, item, sep, tokens, pos, [])
  }
}

fn parse_token_kind(tokens: List(Token), pos: Int, kind: String) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == kind -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_keyword_value(tokens: List(Token), pos: Int, value: String) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == "Operator" && token.value == value -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_ref(g: Grammar(a), name: String, tokens: List(Token), pos: Int) -> Result(InternalResult(a), Nil) {
  case dict.get(g.rules, name) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, pos) {
        Ok(result) -> {
          // Apply the constructor to get the actual AST
          let ast = rule.constructor(result.children)
          Ok(InternalResult(children: [ChildAST(ast)], pos: result.pos))
        }
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_seq(
  g: Grammar(a),
  symbols: List(Symbol),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case symbols {
    [] -> Ok(InternalResult(children: children, pos: pos))
    [sym, ..rest] -> {
      case parse_symbol(g, sym, tokens, pos) {
        Ok(result) -> parse_seq(g, rest, tokens, result.pos, list.append(children, result.children))
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_choice(
  g: Grammar(a),
  alts: List(Symbol),
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case alts {
    [] -> Error(Nil)
    [alt, ..rest] -> {
      case parse_symbol(g, alt, tokens, pos) {
        Ok(result) -> Ok(result)
        Error(_) -> parse_choice(g, rest, tokens, pos)
      }
    }
  }
}

fn parse_opt(
  g: Grammar(a),
  sym: Symbol,
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sym, tokens, pos) {
    Ok(result) -> Ok(result)
    Error(_) -> Ok(InternalResult(children: [], pos: pos))
  }
}

fn parse_many(
  g: Grammar(a),
  sym: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sym, tokens, pos) {
    Ok(result) -> parse_many(g, sym, tokens, result.pos, list.append(children, result.children))
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) -> parse_sep_loop(g, item, sep, tokens, result.pos, list.append(result.children, children))
    Error(_) -> Ok(InternalResult(children: list.reverse(children), pos: pos))
  }
}

fn parse_sep_loop(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sep, tokens, pos) {
    Ok(_) -> {
      case parse_symbol(g, item, tokens, pos) {
        Ok(result) -> parse_sep_loop(g, item, sep, tokens, result.pos, list.append(result.children, children))
        Error(_) -> Ok(InternalResult(children: list.reverse(children), pos: pos))
      }
    }
    Error(_) -> Ok(InternalResult(children: list.reverse(children), pos: pos))
  }
}

fn parse_sep1(
  g: Grammar(a),
  item: Symbol,
  sep: Symbol,
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) -> {
      parse_sep_loop(g, item, sep, tokens, result.pos, list.append(result.children, children))
    }
    Error(_) -> Error(Nil)
  }
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
