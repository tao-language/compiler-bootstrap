// ============================================================================
// GRAMMAR - Declarative Grammar DSL with Pratt Parsing
// ============================================================================
/// A declarative grammar DSL that generates parsers and formatters.
///
/// Features:
/// - Simple, ergonomic API
/// - Support for both C-style and indentation-based languages
/// - Automatic parser and formatter generation
/// - Full Pratt parsing for expression precedence
/// - Built-in comment handling
///
/// # Example
///
/// ```gleam
/// import grammar
///
/// // Define a simple expression grammar
/// let g = grammar.new("Expr")
///   |> grammar.rule("Expr", grammar.expr([
///        grammar.atom("Number"),
///        grammar.infix_l("+", 10),
///        grammar.infix_l("*", 20),
///      ]))
///
/// // Generate parser
/// let parse = grammar.to_parser(g)
/// ```

import gleam/dict.{type Dict}
import gleam/int
import gleam/list
import gleam/option.{Some, None}
import parser.{type Parser, type ParseResult, type Token, type Tree, type ExprOp}
import formatter.{type Doc}

// ============================================================================
// TYPES
// ============================================================================

/// Grammar definition
pub type Grammar {
  Grammar(
    name: String,
    start: String,
    rules: Dict(String, Rule),
    tokens: List(String),
    keywords: List(String),
    indent_sensitive: Bool,
  )
}

/// Grammar rule
pub type Rule {
  Rule(name: String, definition: Symbol)
}

/// Grammar symbol
pub type Symbol {
  /// Match token kind
  Token(String)
  /// Match keyword
  Keyword(String)
  /// Reference another rule
  Ref(String)
  /// Sequence of symbols
  Seq(List(Symbol))
  /// Choice between alternatives
  Choice(List(Symbol))
  /// Optional (zero or one)
  Opt(Symbol)
  /// Zero or more
  Many(Symbol)
  /// One or more
  Many1(Symbol)
  /// Separated list
  Sep(Symbol, Symbol)
  /// Separated list (one or more)
  Sep1(Symbol, Symbol)
  /// Pratt expression with operators
  Expr(List(ExprOp))
  /// Indentation block
  IndentBlock(Symbol)
  /// Labeled symbol (for AST construction)
  Label(String, Symbol)
}

// ============================================================================
// GRAMMAR CONSTRUCTION
// ============================================================================

/// Create new grammar
pub fn new(name: String) -> Grammar {
  Grammar(
    name: name,
    start: "Start",
    rules: dict.new(),
    tokens: [],
    keywords: [],
    indent_sensitive: False,
  )
}

/// Set start rule
pub fn start(g: Grammar, rule: String) -> Grammar {
  Grammar(..g, start: rule)
}

/// Enable indentation-sensitive parsing (Python-style)
pub fn indent_sensitive(g: Grammar) -> Grammar {
  Grammar(..g, indent_sensitive: True)
}

/// Add token kind
pub fn with_token(g: Grammar, kind: String) -> Grammar {
  Grammar(..g, tokens: [kind, ..g.tokens])
}

/// Add keyword
pub fn with_keyword(g: Grammar, kw: String) -> Grammar {
  Grammar(..g, keywords: [kw, ..g.keywords])
}

/// Add rule
pub fn rule(g: Grammar, name: String, def: Symbol) -> Grammar {
  let new_rules = dict.insert(g.rules, name, Rule(name, def))
  Grammar(..g, rules: new_rules)
}

// ============================================================================
// SYMBOL CONSTRUCTORS
// ============================================================================

/// Match token kind
pub fn token(kind: String) -> Symbol {
  Token(kind)
}

/// Match keyword
pub fn keyword(kw: String) -> Symbol {
  Keyword(kw)
}

/// Reference rule
pub fn ref(name: String) -> Symbol {
  Ref(name)
}

/// Sequence
pub fn seq(symbols: List(Symbol)) -> Symbol {
  Seq(symbols)
}

/// Choice
pub fn choice(alts: List(Symbol)) -> Symbol {
  Choice(alts)
}

/// Optional
pub fn opt(sym: Symbol) -> Symbol {
  Opt(sym)
}

/// Zero or more
pub fn many(sym: Symbol) -> Symbol {
  Many(sym)
}

/// One or more
pub fn many1(sym: Symbol) -> Symbol {
  Many1(sym)
}

/// Separated list
pub fn sep(item: Symbol, sep: Symbol) -> Symbol {
  Sep(item, sep)
}

/// Separated list (one or more)
pub fn sep1(item: Symbol, sep: Symbol) -> Symbol {
  Sep1(item, sep)
}

/// Comma-separated list
pub fn comma_sep(item: Symbol) -> Symbol {
  Sep1(item, Token("Comma"))
}

/// Expression with Pratt parsing
pub fn expr(ops: List(ExprOp)) -> Symbol {
  Expr(ops)
}

/// Indentation block
pub fn indent_block(sym: Symbol) -> Symbol {
  IndentBlock(sym)
}

/// Labeled symbol
pub fn label(name: String, sym: Symbol) -> Symbol {
  Label(name, sym)
}

// ============================================================================
// EXPRESSION OPERATORS
// Note: ExprOp constructors are defined in parser module
// Use parser.atom(), parser.prefix(), parser.infix_l(), etc.

// ============================================================================
// PARSER GENERATION
// ============================================================================

/// Convert grammar to parser
pub fn to_parser(g: Grammar) -> fn(List(Token)) -> ParseResult(Tree) {
  let rules_dict = g.rules
  let parser = compile_rule(rules_dict, g.start)
  fn(tokens) { parser.parse(parser, "input", tokens) }
}

/// Compile rule to parser
fn compile_rule(rules: Dict(String, Rule), name: String) -> Parser(Tree) {
  case dict.get(rules, name) {
    Ok(rule) -> compile_symbol(rules, rule.definition, name)
    Error(_) -> parser.fail("undefined rule: " <> name)
  }
}

/// Compile symbol to parser
fn compile_symbol(rules: Dict(String, Rule), sym: Symbol, rule_name: String) -> Parser(Tree) {
  case sym {
    Token(kind) ->
      parser.map(parser.token(kind), fn(tok) { parser.Leaf(tok) })
    Keyword(kw) ->
      parser.map(parser.keyword(kw), fn(tok) { parser.Leaf(tok) })
    Ref(name) ->
      compile_rule(rules, name)
    Seq(symbols) ->
      compile_seq(rules, symbols, rule_name)
    Choice(alts) ->
      parser.one_of(list.map(alts, fn(s) { compile_symbol(rules, s, rule_name) }))
    Opt(sym) ->
      parser.map(parser.opt(compile_symbol(rules, sym, rule_name)), fn(opt) {
        case opt {
          Some(tree) -> tree
          None -> parser.Empty
        }
      })
    Many(sym) ->
      parser.map(
        parser.many(compile_symbol(rules, sym, rule_name)),
        fn(trees) { parser.Node("Many", trees) }
      )
    Many1(sym) ->
      parser.map(
        parser.many1(compile_symbol(rules, sym, rule_name)),
        fn(trees) { parser.Node("Many", trees) }
      )
    Sep(item, sep_sym) ->
      parser.map(
        parser.sep_by(
          compile_symbol(rules, item, rule_name),
          compile_symbol(rules, sep_sym, rule_name)
        ),
        fn(trees) { parser.Node("Sep", trees) }
      )
    Sep1(item, sep_sym) ->
      parser.map(
        parser.sep_by1(
          compile_symbol(rules, item, rule_name),
          compile_symbol(rules, sep_sym, rule_name)
        ),
        fn(trees) { parser.Node("Sep", trees) }
      )
    Expr(ops) ->
      parser.pratt(ops)
    IndentBlock(sym) ->
      compile_indent_block(rules, sym, rule_name)
    Label(name, inner) ->
      parser.map(
        compile_symbol(rules, inner, rule_name),
        fn(tree) { parser.Node(name, [tree]) }
      )
  }
}

/// Compile sequence
fn compile_seq(rules: Dict(String, Rule), symbols: List(Symbol), rule_name: String) -> Parser(Tree) {
  let parsers = list.map(symbols, fn(s) { compile_symbol(rules, s, rule_name) })
  parser.map(parser.seq(parsers), fn(trees) {
    parser.Node("Seq", trees)
  })
}

/// Compile indentation block
fn compile_indent_block(rules: Dict(String, Rule), sym: Symbol, rule_name: String) -> Parser(Tree) {
  // For now, just compile the inner symbol
  // Full implementation would track indentation levels
  compile_symbol(rules, sym, rule_name)
}

// ============================================================================
// FORMATTER GENERATION
// ============================================================================

/// Convert grammar to formatter
pub fn to_formatter(_g: Grammar) -> fn(Tree) -> String {
  fn(tree) {
    let doc = format_tree(tree)
    formatter.render_default(doc)
  }
}

/// Format parse tree
fn format_tree(tree: Tree) -> Doc {
  case tree {
    parser.Leaf(token) -> formatter.text(token.value)
    parser.Node(name, children) -> format_node(name, children)
    parser.Empty -> formatter.empty()
  }
}

/// Format node
fn format_node(name: String, children: List(Tree)) -> Doc {
  case name {
    "Seq" | "Many" | "Sep" ->
      formatter.hsep(list.map(children, format_tree))
    "Prefix" ->
      case children {
        [op, expr] -> formatter.concat([format_tree(op), formatter.space(), format_tree(expr)])
        _ -> formatter.hsep(list.map(children, format_tree))
      }
    "Infix" ->
      case children {
        [left, op, right] -> formatter.hsep([format_tree(left), format_tree(op), format_tree(right)])
        _ -> formatter.hsep(list.map(children, format_tree))
      }
    _ ->
      formatter.hsep(list.map(children, format_tree))
  }
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Get rule names
pub fn rule_names(g: Grammar) -> List(String) {
  dict.keys(g.rules)
}

/// Validate grammar
pub fn validate(g: Grammar) -> Result(Nil, List(String)) {
  let errors = find_undefined_refs(g, g.start, [])
  case errors {
    [] -> Ok(Nil)
    _ -> Error(errors)
  }
}

fn find_undefined_refs(g: Grammar, rule: String, visited: List(String)) -> List(String) {
  case list.contains(visited, rule) {
    True -> []  // Already visited, skip
    False ->
      case dict.get(g.rules, rule) {
        Ok(r) -> find_refs_in_symbol(g, r.definition, [rule, ..visited])
        Error(_) -> ["undefined rule: " <> rule]
      }
  }
}

fn find_refs_in_symbol(g: Grammar, sym: Symbol, visited: List(String)) -> List(String) {
  case sym {
    Ref(name) -> find_undefined_refs(g, name, visited)
    Seq(symbols) -> list.flat_map(symbols, fn(s) { find_refs_in_symbol(g, s, visited) })
    Choice(alts) -> list.flat_map(alts, fn(s) { find_refs_in_symbol(g, s, visited) })
    Opt(s) -> find_refs_in_symbol(g, s, visited)
    Many(s) -> find_refs_in_symbol(g, s, visited)
    Many1(s) -> find_refs_in_symbol(g, s, visited)
    Sep(item, sep) -> 
      list.append(
        find_refs_in_symbol(g, item, visited),
        find_refs_in_symbol(g, sep, visited)
      )
    Sep1(item, sep) -> 
      list.append(
        find_refs_in_symbol(g, item, visited),
        find_refs_in_symbol(g, sep, visited)
      )
    Expr(_) -> []
    IndentBlock(s) -> find_refs_in_symbol(g, s, visited)
    Label(_, s) -> find_refs_in_symbol(g, s, visited)
    Token(_) -> []
    Keyword(_) -> []
  }
}
