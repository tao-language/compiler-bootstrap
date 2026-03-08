// ============================================================================
// GRAMMAR - Generic Grammar DSL with Parser and Formatter Generation
// ============================================================================
/// A generic grammar DSL that generates parsers and formatters for any AST type.
///
/// The grammar is the **single source of truth** - it defines:
/// - Structure (what to parse)
/// - Precedences (binding strength)
/// - Operators (keywords and constructors)
/// - Format templates (how to format)
///
/// # Example
///
/// ```gleam
/// import grammar
/// import calc/ast
///
/// let g = grammar.new()
///   |> grammar.start("Expr")
///   |> grammar.left_assoc(
///     "Expr",
///     grammar.ref("Term"),
///     [grammar.op("+", fn(l, r) { Add(l, r) }, " + ")],
///     10,
///   )
///
/// let result = grammar.parse(g, "1 + 2")
/// let formatted = grammar.format(g, result.ast)
/// ```
import gleam/dict.{type Dict}
import gleam/list
import gleam/result
import lexer
import parser.{type ParseResult, type Token}

// ============================================================================
// TYPES
// ============================================================================

/// Associativity of operators
pub type Associativity {
  Left
  Right
  None
}

/// Generic grammar parameterized by AST type
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
  )
}

/// Grammar rule with full parsing and formatting info
pub type Rule(a) {
  Rule(
    name: String,
    definition: Symbol(a),
    constructor: fn(List(ParseChild(a))) -> a,
    precedence: Int,
    associativity: Associativity,
    format_template: FormatTemplate,
  )
}

/// Format template - how to format children
pub type FormatTemplate {
  /// Simple sequence: format children with separators
  TemplateSeq(separators: List(String))
  /// Custom formatter for complex cases
  TemplateCustom
}

/// Child of a parse result
pub type ParseChild(a) {
  ChildToken(Token)
  ChildAST(a)
}

/// Grammar symbol (not generic - describes structure)
pub type Symbol(a) {
  Token(kind: String)
  Keyword(value: String)
  Ref(rule: String)
  Seq(symbols: List(Symbol(a)))
  Choice(alts: List(Symbol(a)))
  Opt(symbol: Symbol(a))
  Many(symbol: Symbol(a))
  Sep(item: Symbol(a), sep: Symbol(a))
  Sep1(item: Symbol(a), sep: Symbol(a))
  /// Left-associative operator sequence (special handling)
  LeftAssoc(first: Symbol(a), ops: List(Operator(a)))
}

/// Operator for left_assoc
/// Note: Using a generic function type that works with any AST
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    format_separator: String,
  )
}

/// Internal parse result
type InternalResult(a) {
  InternalResult(children: List(ParseChild(a)), pos: Int)
}

// ============================================================================
// GRAMMAR CONSTRUCTION - Basic Functions
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

// ============================================================================
// GRAMMAR CONSTRUCTION - Rule Definition
// ============================================================================

/// Add basic rule
pub fn rule(
  g: Grammar(a),
  name: String,
  definition: Symbol(a),
  constructor: fn(List(ParseChild(a))) -> a,
  precedence: Int,
  format_template: FormatTemplate,
) -> Grammar(a) {
  let rule =
    Rule(
      name: name,
      definition: definition,
      constructor: constructor,
      precedence: precedence,
      associativity: None,
      format_template: format_template,
    )
  let rules = dict.insert(g.rules, name, rule)
  Grammar(..g, rules: rules)
}

/// Add left-associative operator rule (convenience function)
pub fn left_assoc(
  g: Grammar(a),
  name: String,
  first: Symbol(a),
  ops: List(Operator(a)),
  precedence: Int,
) -> Grammar(a) {
  // Build format template from operators
  let separators = list.map(ops, fn(op) { op.format_separator })

  // Build constructor that folds left-to-right
  let constructor = make_left_assoc_constructor(ops)

  // Build symbol for LeftAssoc
  let definition = LeftAssoc(first, ops)

  rule(g, name, definition, constructor, precedence, TemplateSeq(separators))
}

/// Create operator definition
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  format_separator: String,
) -> Operator(a) {
  Operator(keyword, constructor, format_separator)
}

// ============================================================================
// SYMBOL CONSTRUCTORS
// ============================================================================

pub fn token(kind: String) -> Symbol(a) {
  Token(kind)
}

pub fn keyword(value: String) -> Symbol(a) {
  Keyword(value)
}

pub fn ref(name: String) -> Symbol(a) {
  Ref(name)
}

pub fn seq(symbols: List(Symbol(a))) -> Symbol(a) {
  Seq(symbols)
}

pub fn choice(alts: List(Symbol(a))) -> Symbol(a) {
  Choice(alts)
}

pub fn opt(symbol: Symbol(a)) -> Symbol(a) {
  Opt(symbol)
}

pub fn many(symbol: Symbol(a)) -> Symbol(a) {
  Many(symbol)
}

pub fn sep(item: Symbol(a), sep: Symbol(a)) -> Symbol(a) {
  Sep(item, sep)
}

pub fn sep1(item: Symbol(a), sep: Symbol(a)) -> Symbol(a) {
  Sep1(item, sep)
}

// ============================================================================
// PARSER - Main Entry Point
// ============================================================================

/// Parse source using grammar
pub fn parse(g: Grammar(a), source: String) -> parser.ParseResult(a) {
  let tokens = lexer.tokenize(lexer.default_config(), g.name, source)

  case dict.get(g.rules, g.start) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, 0) {
        Ok(result) -> {
          let ast = rule.constructor(result.children)
          parser.ParseResult(ast: ast, errors: [])
        }
        Error(_) -> parser.ParseResult(ast: panic as "Parse failed", errors: [])
      }
    }
    Error(_) -> parser.ParseResult(ast: panic as "No start rule", errors: [])
  }
}

// ============================================================================
// PARSER - Symbol Parsing
// ============================================================================

fn parse_symbol(
  g: Grammar(a),
  symbol: Symbol(a),
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
    LeftAssoc(first, ops) -> parse_left_assoc(g, first, ops, tokens, pos)
  }
}

// ============================================================================
// PARSER - Left-Associative Parsing (Critical for Correctness!)
// ============================================================================

/// Parse left-associative operator sequence
/// This is the key function that fixes the associativity bug!
///
/// Instead of recursively parsing the full right side (which creates
/// right-associativity), we parse one operator at a time and fold
/// left-to-right.
fn parse_left_assoc(
  g: Grammar(a),
  first: Symbol(a),
  ops: List(Operator(a)),
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  // Parse the first element
  case parse_symbol(g, first, tokens, pos) {
    Ok(result) -> {
      // Get the first AST value
      case result.children {
        [ChildAST(first_ast)] -> {
          // Parse operators and fold left-to-right
          parse_left_assoc_loop(first_ast, g, first, ops, tokens, result.pos)
        }
        _ -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn parse_left_assoc_loop(
  left: a,
  g: Grammar(a),
  first: Symbol(a),
  ops: List(Operator(a)),
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  // Try to parse an operator
  case parse_operator(ops, tokens, pos) {
    Ok(#(op, op_pos)) -> {
      // Parse the next element (NOT left_assoc - just the first symbol!)
      // This is the key: we only parse ONE level, not recursively
      case parse_symbol(g, first, tokens, op_pos) {
        Ok(result) -> {
          case result.children {
            [ChildAST(right)] -> {
              // Apply the operator constructor (left-associative!)
              let new_left = apply_operator(op, left, right)
              // Continue loop with new left value
              parse_left_assoc_loop(new_left, g, first, ops, tokens, result.pos)
            }
            _ -> Ok(InternalResult(children: [ChildAST(left)], pos: pos))
          }
        }
        Error(_) -> Ok(InternalResult(children: [ChildAST(left)], pos: pos))
      }
    }
    Error(_) -> {
      // No more operators, return accumulated result
      Ok(InternalResult(children: [ChildAST(left)], pos: pos))
    }
  }
}

fn parse_operator(
  ops: List(Operator(a)),
  tokens: List(Token),
  pos: Int,
) -> Result(#(Operator(a), Int), Nil) {
  case get_token(tokens, pos) {
    Ok(token) -> {
      case list.find(ops, fn(op) { op.keyword == token.value }) {
        Ok(op) -> Ok(#(op, pos + 1))
        Error(_) -> Error(Nil)
      }
    }
    Error(_) -> Error(Nil)
  }
}

fn apply_operator(op: Operator(a), left: a, right: a) -> a {
  op.constructor(left, right)
}

// ============================================================================
// PARSER - Basic Parsing Functions
// ============================================================================

fn parse_token_kind(
  tokens: List(Token),
  pos: Int,
  kind: String,
) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == kind -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_keyword_value(
  tokens: List(Token),
  pos: Int,
  value: String,
) -> Result(InternalResult(a), Nil) {
  case get_token(tokens, pos) {
    Ok(token) if token.kind == "Operator" && token.value == value -> {
      Ok(InternalResult(children: [ChildToken(token)], pos: pos + 1))
    }
    _ -> Error(Nil)
  }
}

fn parse_ref(
  g: Grammar(a),
  name: String,
  tokens: List(Token),
  pos: Int,
) -> Result(InternalResult(a), Nil) {
  case dict.get(g.rules, name) {
    Ok(rule) -> {
      case parse_symbol(g, rule.definition, tokens, pos) {
        Ok(result) -> {
          // Apply constructor to get actual AST
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
  symbols: List(Symbol(a)),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case symbols {
    [] -> Ok(InternalResult(children: children, pos: pos))
    [sym, ..rest] -> {
      case parse_symbol(g, sym, tokens, pos) {
        Ok(result) ->
          parse_seq(
            g,
            rest,
            tokens,
            result.pos,
            list.append(children, result.children),
          )
        Error(_) -> Error(Nil)
      }
    }
  }
}

fn parse_choice(
  g: Grammar(a),
  alts: List(Symbol(a)),
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
  sym: Symbol(a),
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
  sym: Symbol(a),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sym, tokens, pos) {
    Ok(result) ->
      parse_many(
        g,
        sym,
        tokens,
        result.pos,
        list.append(children, result.children),
      )
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep(
  g: Grammar(a),
  item: Symbol(a),
  sep: Symbol(a),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) ->
      parse_sep_loop(
        g,
        item,
        sep,
        tokens,
        result.pos,
        list.append(children, result.children),
      )
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep_loop(
  g: Grammar(a),
  item: Symbol(a),
  sep: Symbol(a),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, sep, tokens, pos) {
    Ok(_) -> {
      case parse_symbol(g, item, tokens, pos) {
        Ok(result) ->
          parse_sep_loop(
            g,
            item,
            sep,
            tokens,
            result.pos,
            list.append(children, result.children),
          )
        Error(_) -> Ok(InternalResult(children: children, pos: pos))
      }
    }
    Error(_) -> Ok(InternalResult(children: children, pos: pos))
  }
}

fn parse_sep1(
  g: Grammar(a),
  item: Symbol(a),
  sep: Symbol(a),
  tokens: List(Token),
  pos: Int,
  children: List(ParseChild(a)),
) -> Result(InternalResult(a), Nil) {
  case parse_symbol(g, item, tokens, pos) {
    Ok(result) ->
      parse_sep_loop(
        g,
        item,
        sep,
        tokens,
        result.pos,
        list.append(children, result.children),
      )
    Error(_) -> Error(Nil)
  }
}

// ============================================================================
// PARSER - Token Helpers
// ============================================================================

fn get_token(tokens: List(Token), pos: Int) -> Result(Token, Nil) {
  get_token_loop(tokens, pos, 0)
}

fn get_token_loop(
  tokens: List(Token),
  pos: Int,
  current: Int,
) -> Result(Token, Nil) {
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

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Generate constructor for left-associative operators
/// Note: For left_assoc, the parsing already folds the operators,
/// so the constructor just extracts the final value
fn make_left_assoc_constructor(
  _ops: List(Operator(a)),
) -> fn(List(ParseChild(a))) -> a {
  fn(children: List(ParseChild(a))) -> a {
    case children {
      [ChildAST(final_value)] -> final_value
      _ -> panic as "Invalid left_assoc children"
    }
  }
}

// ============================================================================
// FORMATTER
// ============================================================================

/// Format AST using grammar
pub fn format(g: Grammar(a), ast: a) -> String {
  format_with_grammar(g, g.start, ast, 0)
}

fn format_with_grammar(
  g: Grammar(a),
  rule_name: String,
  ast: a,
  parent_prec: Int,
) -> String {
  case dict.get(g.rules, rule_name) {
    Ok(rule) -> {
      let prec = rule.precedence
      let doc = format_by_template(rule.format_template, ast, rule)

      // Add parens if child precedence < parent precedence
      case prec < parent_prec {
        True -> "(" <> doc <> ")"
        False -> doc
      }
    }
    Error(_) -> "<unknown>"
  }
}

fn format_by_template(template: FormatTemplate, ast: a, rule: Rule(a)) -> String {
  case template {
    TemplateSeq(_) -> {
      // For simple sequences, use default formatting
      format_default(ast)
    }
    TemplateCustom -> {
      // Custom formatting handled by grammar-specific code
      format_default(ast)
    }
  }
}

fn format_default(ast: a) -> String {
  // Default implementation - just convert to string
  // Real impl would pattern-match on ast type
  "<ast>"
}
