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
import formatter.{type Doc}
import gleam/dict.{type Dict}
import gleam/list
import gleam/option.{None, Some}
import parser.{type ExprOp, type ParseResult, type Parser, type Token, type Tree}

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
// PARSER GENERATION
// ============================================================================

/// Compilation state with cache for recursive rules
type CompileState {
  CompileState(rules: Dict(String, Rule), compiled: Dict(String, Parser(Tree)))
}

/// Convert grammar to parser
pub fn to_parser(g: Grammar) -> fn(List(Token)) -> ParseResult(Tree) {
  let rules_dict = g.rules
  let initial_state = CompileState(rules: rules_dict, compiled: dict.new())
  let #(parser, _) = compile_rule(g.start, initial_state)
  fn(tokens) { parser.parse(parser, "input", tokens) }
}

/// Compile rule with caching for recursion
fn compile_rule(
  name: String,
  state: CompileState,
) -> #(Parser(Tree), CompileState) {
  // Check if already compiled (handles recursion)
  case dict.get(state.compiled, name) {
    Ok(parser) -> #(parser, state)
    Error(_) -> {
      // Add placeholder to break recursion cycle
      let placeholder = parser.fail("compiling: " <> name)
      let state =
        CompileState(
          ..state,
          compiled: dict.insert(state.compiled, name, placeholder),
        )

      // Get rule definition
      case dict.get(state.rules, name) {
        Ok(rule) -> {
          // Compile the actual parser
          let #(actual, state) = compile_symbol(rule.definition, name, state)
          // Update cache with real parser
          let state =
            CompileState(
              ..state,
              compiled: dict.insert(state.compiled, name, actual),
            )
          #(actual, state)
        }
        Error(_) -> {
          let error_parser = parser.fail("undefined rule: " <> name)
          #(error_parser, state)
        }
      }
    }
  }
}

/// Compile symbol to parser
fn compile_symbol(
  sym: Symbol,
  rule_name: String,
  state: CompileState,
) -> #(Parser(Tree), CompileState) {
  case sym {
    Token(kind) -> {
      let p = parser.map(parser.token(kind), fn(tok) { parser.Leaf(tok) })
      #(p, state)
    }
    Keyword(kw) -> {
      let p = parser.map(parser.keyword(kw), fn(tok) { parser.Leaf(tok) })
      #(p, state)
    }
    Ref(name) -> {
      compile_rule(name, state)
    }
    Seq(symbols) -> {
      compile_seq(symbols, rule_name, state)
    }
    Choice(alts) -> {
      let #(parsers, state) = compile_symbols(alts, rule_name, state)
      #(parser.one_of(parsers), state)
    }
    Opt(sym) -> {
      let #(p, state) = compile_symbol(sym, rule_name, state)
      #(
        parser.map(parser.opt(p), fn(opt) {
          case opt {
            Some(tree) -> tree
            None -> parser.Empty
          }
        }),
        state,
      )
    }
    Many(sym) -> {
      let #(p, state) = compile_symbol(sym, rule_name, state)
      #(
        parser.map(parser.many(p), fn(trees) { parser.Node("Many", trees) }),
        state,
      )
    }
    Many1(sym) -> {
      let #(p, state) = compile_symbol(sym, rule_name, state)
      #(
        parser.map(parser.many1(p), fn(trees) { parser.Node("Many", trees) }),
        state,
      )
    }
    Sep(item, sep_sym) -> {
      let #(p_item, state) = compile_symbol(item, rule_name, state)
      let #(p_sep, state) = compile_symbol(sep_sym, rule_name, state)
      #(
        parser.map(parser.sep_by(p_item, p_sep), fn(trees) {
          parser.Node("Sep", trees)
        }),
        state,
      )
    }
    Sep1(item, sep_sym) -> {
      let #(p_item, state) = compile_symbol(item, rule_name, state)
      let #(p_sep, state) = compile_symbol(sep_sym, rule_name, state)
      #(
        parser.map(parser.sep_by1(p_item, p_sep), fn(trees) {
          parser.Node("Sep", trees)
        }),
        state,
      )
    }
    Expr(ops) -> {
      #(parser.pratt(ops), state)
    }
    IndentBlock(sym) -> {
      compile_indent_block(sym, rule_name, state)
    }
    Label(name, inner) -> {
      let #(p, state) = compile_symbol(inner, rule_name, state)
      #(parser.map(p, fn(tree) { parser.Node(name, [tree]) }), state)
    }
  }
}

/// Compile multiple symbols
fn compile_symbols(
  symbols: List(Symbol),
  rule_name: String,
  state: CompileState,
) -> #(List(Parser(Tree)), CompileState) {
  compile_symbols_loop(symbols, rule_name, state, [])
}

fn compile_symbols_loop(
  symbols: List(Symbol),
  rule_name: String,
  state: CompileState,
  acc: List(Parser(Tree)),
) -> #(List(Parser(Tree)), CompileState) {
  case symbols {
    [] -> #(list.reverse(acc), state)
    [sym, ..rest] -> {
      let #(p, state) = compile_symbol(sym, rule_name, state)
      compile_symbols_loop(rest, rule_name, state, [p, ..acc])
    }
  }
}

/// Compile sequence
fn compile_seq(
  symbols: List(Symbol),
  rule_name: String,
  state: CompileState,
) -> #(Parser(Tree), CompileState) {
  let #(parsers, state) = compile_symbols(symbols, rule_name, state)
  #(
    parser.map(parser.seq(parsers), fn(trees) { parser.Node("Seq", trees) }),
    state,
  )
}

/// Compile indentation block
fn compile_indent_block(
  sym: Symbol,
  rule_name: String,
  state: CompileState,
) -> #(Parser(Tree), CompileState) {
  // For now, just compile the inner symbol
  // Full implementation would track indentation levels
  compile_symbol(sym, rule_name, state)
}

// ============================================================================
// FORMATTER GENERATION
// ============================================================================

/// Format configuration
pub type FormatConfig {
  FormatConfig(
    /// Indentation width (spaces)
    indent_width: Int,
    /// Maximum line width before breaking
    max_width: Int,
    /// Use spaces for indentation
    spaces: Bool,
  )
}

/// Default format configuration
pub fn default_config() -> FormatConfig {
  FormatConfig(indent_width: 2, max_width: 80, spaces: True)
}

/// Convert grammar to formatter with default config
pub fn to_formatter(g: Grammar) -> fn(Tree) -> String {
  to_formatter_with_config(g, default_config())
}

/// Convert grammar to formatter with custom config
pub fn to_formatter_with_config(
  g: Grammar,
  config: FormatConfig,
) -> fn(Tree) -> String {
  let rules = g.rules
  fn(tree) {
    let doc = format_tree_with_rules(tree, rules, config)
    formatter.render(doc, config.max_width)
  }
}

/// Format parse tree using grammar rules
fn format_tree_with_rules(
  tree: Tree,
  rules: Dict(String, Rule),
  config: FormatConfig,
) -> Doc {
  format_tree_with_rules_indent(tree, rules, config, 0)
}

fn format_tree_with_rules_indent(
  tree: Tree,
  rules: Dict(String, Rule),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  case tree {
    parser.Leaf(token) -> format_token(token)
    parser.Node(name, children) ->
      format_node_with_rules_indent(name, children, rules, config, indent)
    parser.Empty -> formatter.empty()
  }
}

/// Format token based on its kind
fn format_token(token: parser.Token) -> Doc {
  case token.kind {
    "Int" | "Float" -> formatter.text(token.value)
    "String" -> formatter.quoted_string(token.value)
    "Bool" -> formatter.text(token.value)
    "Ident" | "Keyword" -> formatter.text(token.value)
    _ -> formatter.text(token.value)
  }
}

/// Format node using grammar rules
fn format_node_with_rules_indent(
  name: String,
  children: List(Tree),
  rules: Dict(String, Rule),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  // Check if this node name matches a grammar rule
  case dict.get(rules, name) {
    Ok(rule) -> format_rule(rule, children, config, indent)
    Error(_) -> format_generic_node(name, children, config, indent)
  }
}

/// Format based on grammar rule
fn format_rule(
  rule: Rule,
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  format_symbol(rule.definition, children, config, indent)
}

/// Format symbol based on its type
fn format_symbol(
  sym: Symbol,
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  case sym {
    Token(_) | Keyword(_) -> {
      // Terminal - should have one child (the token)
      case children {
        [child] ->
          format_tree_with_rules_indent(child, dict.new(), config, indent)
        _ -> formatter.empty()
      }
    }
    Seq(_) -> format_sequence(children, config, indent)
    Choice(_) -> format_choice(children, config, indent)
    Opt(_) -> format_optional(children, config, indent)
    Many(_) | Many1(_) -> format_repetition(children, config, indent)
    Sep(_, _) -> format_separated(children, config, indent)
    Sep1(_, _) -> format_separated(children, config, indent)
    Expr(_) -> format_expression(children, config, indent)
    IndentBlock(_) -> format_indented_block(children, config, indent)
    Label(_, inner) -> format_symbol(inner, children, config, indent)
    Ref(_) -> format_generic_node("Ref", children, config, indent)
  }
}

/// Format sequence of children
fn format_sequence(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  formatter.hsep(
    list.map(children, fn(c) {
      format_tree_with_rules_indent(c, dict.new(), config, indent)
    }),
  )
}

/// Format choice (just format the chosen alternative)
fn format_choice(children: List(Tree), config: FormatConfig, indent: Int) -> Doc {
  case children {
    [child] -> format_tree_with_rules_indent(child, dict.new(), config, indent)
    _ ->
      formatter.hsep(list.map(
        children,
        format_tree_with_rules_child(config, indent),
      ))
  }
}

fn format_tree_with_rules_child(
  config: FormatConfig,
  indent: Int,
) -> fn(Tree) -> Doc {
  fn(c) { format_tree_with_rules_indent(c, dict.new(), config, indent) }
}

/// Format optional (skip empty children)
fn format_optional(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  case children {
    [] -> formatter.empty()
    [child] -> format_tree_with_rules_indent(child, dict.new(), config, indent)
    _ ->
      formatter.hsep(list.map(
        children,
        format_tree_with_rules_child(config, indent),
      ))
  }
}

/// Format repetition (space-separated)
fn format_repetition(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  formatter.hsep(list.map(
    children,
    format_tree_with_rules_child(config, indent),
  ))
}

/// Format separated list
fn format_separated(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  formatter.comma_sep(list.map(
    children,
    format_tree_with_rules_child(config, indent),
  ))
}

/// Format expression (use precedence-aware formatting)
fn format_expression(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  formatter.hsep(list.map(
    children,
    format_tree_with_rules_child(config, indent),
  ))
}

/// Format indented block
fn format_indented_block(
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  formatter.braces(formatter.nest(
    config.indent_width,
    formatter.vsep(list.map(
      children,
      format_tree_with_rules_child(config, indent + config.indent_width),
    )),
  ))
}

/// Format generic node (fallback for unknown nodes)
fn format_generic_node(
  name: String,
  children: List(Tree),
  config: FormatConfig,
  indent: Int,
) -> Doc {
  case children {
    [] -> formatter.text(name)
    _ ->
      formatter.hsep(list.map(
        children,
        format_tree_with_rules_child(config, indent),
      ))
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

fn find_undefined_refs(
  g: Grammar,
  rule: String,
  visited: List(String),
) -> List(String) {
  case list.contains(visited, rule) {
    True -> []
    // Already visited, skip
    False ->
      case dict.get(g.rules, rule) {
        Ok(r) -> find_refs_in_symbol(g, r.definition, [rule, ..visited])
        Error(_) -> ["undefined rule: " <> rule]
      }
  }
}

fn find_refs_in_symbol(
  g: Grammar,
  sym: Symbol,
  visited: List(String),
) -> List(String) {
  case sym {
    Ref(name) -> find_undefined_refs(g, name, visited)
    Seq(symbols) ->
      list.flat_map(symbols, fn(s) { find_refs_in_symbol(g, s, visited) })
    Choice(alts) ->
      list.flat_map(alts, fn(s) { find_refs_in_symbol(g, s, visited) })
    Opt(s) -> find_refs_in_symbol(g, s, visited)
    Many(s) -> find_refs_in_symbol(g, s, visited)
    Many1(s) -> find_refs_in_symbol(g, s, visited)
    Sep(item, sep) ->
      list.append(
        find_refs_in_symbol(g, item, visited),
        find_refs_in_symbol(g, sep, visited),
      )
    Sep1(item, sep) ->
      list.append(
        find_refs_in_symbol(g, item, visited),
        find_refs_in_symbol(g, sep, visited),
      )
    Expr(_) -> []
    IndentBlock(s) -> find_refs_in_symbol(g, s, visited)
    Label(_, s) -> find_refs_in_symbol(g, s, visited)
    Token(_) -> []
    Keyword(_) -> []
  }
}
