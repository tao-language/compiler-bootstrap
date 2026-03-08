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
import formatter.{type Doc}
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

/// Layout style for formatting
pub type LayoutStyle {
  /// All on one line: `a + b`
  Inline
  /// Break after operator, indent: `a\n  + b`
  BreakAfterOperator(indent: Int)
  /// Break before operator: `a\n+ b`
  BreakBeforeOperator(indent: Int)
  /// Block style: `{\n  x: 1,\n}`
  Block(open: String, close: String, indent: Int)
  /// Custom formatter function
  Custom
}

/// Operator information for formatting
pub type OperatorInfo(a) {
  OperatorInfo(
    precedence: Int,
    associativity: Associativity,
    separator: String,
    layout: LayoutStyle,
    format_fn: fn(a, a, Int, fn(a, Int) -> Doc) -> Doc,
  )
}

/// Generic grammar parameterized by AST type
pub type Grammar(a) {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule(a)),
    tokens: List(String),
    keywords: List(String),
    /// Operator information for formatting (runtime lookup table)
    operator_info: Dict(String, OperatorInfo(a)),
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

/// Operator for left_assoc with full formatting info
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,
    format_separator: String,
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
    format_fn: fn(a, a, Int, fn(a, Int) -> Doc) -> Doc,
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
    operator_info: dict.new(),
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

  // Build operator info dict for formatting
  let operator_info =
    list.fold(ops, g.operator_info, fn(acc, op) {
      dict.insert(
        acc,
        op.keyword,
        OperatorInfo(
          op.precedence,
          op.associativity,
          op.format_separator,
          op.layout,
          op.format_fn,
        ),
      )
    })

  let g =
    rule(g, name, definition, constructor, precedence, TemplateSeq(separators))
  Grammar(..g, operator_info: operator_info)
}

/// Create operator definition with full formatting info
pub fn op(
  keyword: String,
  constructor: fn(a, a) -> a,
  format_separator: String,
  precedence: Int,
  associativity: Associativity,
  layout: LayoutStyle,
) -> Operator(a) {
  // Create format function that handles precedence & parenthesization
  let format_fn = fn(
    left: a,
    right: a,
    parent_prec: Int,
    format_child: fn(a, Int) -> Doc,
  ) {
    let doc = case associativity {
      Left -> {
        let l_doc = format_child(left, precedence + 1)
        let r_doc = format_child(right, precedence)
        format_binop(
          l_doc,
          r_doc,
          format_separator,
          precedence,
          parent_prec,
          layout,
        )
      }
      Right -> {
        let l_doc = format_child(left, precedence)
        let r_doc = format_child(right, precedence + 1)
        format_binop(
          l_doc,
          r_doc,
          format_separator,
          precedence,
          parent_prec,
          layout,
        )
      }
      None -> {
        let l_doc = format_child(left, precedence)
        let r_doc = format_child(right, precedence)
        format_binop(
          l_doc,
          r_doc,
          format_separator,
          precedence,
          parent_prec,
          layout,
        )
      }
    }
    doc
  }

  Operator(
    keyword,
    constructor,
    format_separator,
    precedence,
    associativity,
    layout,
    format_fn,
  )
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
// FORMATTER COMBINATORS
// ============================================================================

/// Generic binary operator formatter with layout support
pub fn format_binop(
  left: Doc,
  right: Doc,
  separator: String,
  precedence: Int,
  parent_prec: Int,
  layout: LayoutStyle,
) -> Doc {
  let doc = case layout {
    Inline -> {
      formatter.concat([
        left,
        formatter.text(separator),
        right,
      ])
    }
    BreakAfterOperator(indent) -> {
      formatter.group(
        formatter.concat([
          left,
          formatter.text(separator),
          formatter.line(),
          formatter.nest(indent, right),
        ]),
      )
    }
    BreakBeforeOperator(indent) -> {
      formatter.group(
        formatter.concat([
          left,
          formatter.line(),
          formatter.nest(
            indent,
            formatter.concat([
              formatter.text(separator),
              right,
            ]),
          ),
        ]),
      )
    }
    Block(_, _, indent) -> {
      formatter.group(
        formatter.concat([
          left,
          formatter.text(separator),
          formatter.line(),
          formatter.nest(indent, right),
        ]),
      )
    }
    Custom -> {
      formatter.concat([
        left,
        formatter.text(separator),
        right,
      ])
    }
  }
  wrap_parens(doc, precedence < parent_prec)
}

/// Block formatter for records, lists, etc.
pub fn format_block(
  open: String,
  children: List(Doc),
  close: String,
  separator: String,
  indent: Int,
  parent_prec: Int,
) -> Doc {
  let children_doc = case children {
    [] -> formatter.text("")
    [first, ..rest] -> {
      formatter.concat(list.append(
        [first],
        list.map(rest, fn(c) {
          formatter.concat([
            formatter.text(separator),
            formatter.line(),
            c,
          ])
        }),
      ))
    }
  }
  formatter.group(
    formatter.concat([
      formatter.text(open),
      formatter.nest(
        indent,
        formatter.concat([
          formatter.line(),
          children_doc,
        ]),
      ),
      formatter.line(),
      formatter.text(close),
    ]),
  )
}

/// Wrap in parens if precedence condition is met
pub fn wrap_parens(doc: Doc, condition: Bool) -> Doc {
  case condition {
    True ->
      formatter.concat([
        formatter.text("("),
        doc,
        formatter.text(")"),
      ])
    False -> doc
  }
}

/// Format any binary operator from grammar (with error message including operator name)
pub fn format_op(
  g: Grammar(a),
  op: String,
  left: a,
  right: a,
  parent_prec: Int,
  format_child: fn(a, Int) -> Doc,
) -> Doc {
  case dict.get(g.operator_info, op) {
    Ok(info) -> info.format_fn(left, right, parent_prec, format_child)
    Error(_) -> formatter.text("<unknown operator: " <> op <> ">")
  }
}

/// Default formatter for block structures (lists, tuples, records)
pub fn format_block_default(
  children: List(a),
  open: String,
  close: String,
  separator: String,
  indent: Int,
  parent_prec: Int,
  format_child: fn(a, Int) -> Doc,
) -> Doc {
  let child_docs = list.map(children, fn(c) { format_child(c, 0) })
  format_block(open, child_docs, close, separator, indent, parent_prec)
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
