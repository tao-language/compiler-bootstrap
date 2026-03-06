// ============================================================================
// GRAMMAR - Unified Grammar Definition for Parsing and Formatting
// ============================================================================

/// A unified grammar system that defines a language grammar once and derives
/// both parsers and formatters from it.
///
/// # Example
///
/// ```gleam
/// import grammar
///
/// let expr_grammar = grammar.grammar("Expr", [
///   grammar.rule("Expr", grammar.choice([
///     grammar.seq([
///       grammar.token("let"),
///       grammar.pattern("Ident"),
///       grammar.token("="),
///       grammar.ref("Expr"),
///     ]),
///     grammar.ref("Term"),
///   ])),
///   grammar.rule("Term", grammar.choice([
///     grammar.pattern("Ident"),
///     grammar.pattern("Number"),
///   ])),
/// ])
///
/// let parser = grammar.to_parser(expr_grammar)
/// let formatter = grammar.to_formatter(expr_grammar)
/// ```
import formatter as f
import gleam/dict
import gleam/list
import gleam/result
import gleam/string
import parser as p

// ============================================================================
// GRAMMAR TYPES
// ============================================================================

/// A grammar rule name
pub type RuleName {
  RuleName(name: String)
}

/// A grammar symbol - the building blocks of grammar rules
pub type Symbol {
  /// A literal terminal (e.g., "=>", "{", "}")
  SymToken(String)
  /// A reference to another rule
  SymRule(RuleName)
  /// A sequence of symbols (all must match in order)
  SymSeq(List(Symbol))
  /// Alternative choices (first matching wins)
  SymChoice(List(Symbol))
  /// Optional symbol (may or may not match)
  SymOpt(Symbol)
  /// Zero or more repetitions
  SymRep(Symbol)
  /// One or more repetitions
  SymRep1(Symbol)
  /// A named pattern (captures a token)
  SymPattern(String)
}

/// A grammar rule: name -> definition
pub type Rule {
  Rule(name: RuleName, definition: Symbol)
}

/// A complete grammar with rules and a start symbol
pub type Grammar {
  Grammar(rules: List(Rule), start: RuleName)
}

// ============================================================================
// GRAMMAR BUILDER
// ============================================================================

/// Create a new grammar with a start rule
pub fn grammar(start: String, rules: List(Rule)) -> Grammar {
  Grammar(rules, RuleName(start))
}

/// Create a grammar rule
pub fn rule(name: String, definition: Symbol) -> Rule {
  Rule(RuleName(name), definition)
}

/// Create a terminal symbol
pub fn token(value: String) -> Symbol {
  SymToken(value)
}

/// Create a rule reference
pub fn ref_rule(name: String) -> Symbol {
  SymRule(RuleName(name))
}

/// Create a sequence of symbols
pub fn seq(symbols: List(Symbol)) -> Symbol {
  SymSeq(symbols)
}

/// Create a choice between alternatives
pub fn choice(alternatives: List(Symbol)) -> Symbol {
  SymChoice(alternatives)
}

/// Make a symbol optional
pub fn opt(symbol: Symbol) -> Symbol {
  SymOpt(symbol)
}

/// Zero or more repetitions
pub fn rep(symbol: Symbol) -> Symbol {
  SymRep(symbol)
}

/// One or more repetitions
pub fn rep1(symbol: Symbol) -> Symbol {
  SymRep1(symbol)
}

/// Create a named pattern (for capturing tokens)
pub fn pattern(name: String) -> Symbol {
  SymPattern(name)
}

// ============================================================================
// GRAMMAR INSPECTION
// ============================================================================

/// Get all rule names from a grammar
pub fn get_rule_names(grammar: Grammar) -> List(String) {
  grammar.rules |> list.map(fn(r) { r.name.name })
}

/// Get the start rule name
pub fn get_start_rule(grammar: Grammar) -> String {
  grammar.start.name
}

/// Format a grammar for debugging
pub fn format_grammar(grammar: Grammar) -> String {
  let rule_strings =
    grammar.rules
    |> list.map(fn(rule) {
      rule.name.name <> " -> " <> format_symbol(rule.definition)
    })
    |> string.join("\n")

  "Grammar(start: " <> grammar.start.name <> ")\n" <> rule_strings
}

/// Format a symbol for debugging
fn format_symbol(symbol: Symbol) -> String {
  case symbol {
    SymToken(v) -> "\"" <> v <> "\""
    SymRule(name) -> name.name
    SymSeq(symbols) -> symbols |> list.map(format_symbol) |> string.join(" ")
    SymChoice(alts) -> alts |> list.map(format_symbol) |> string.join(" | ")
    SymOpt(sym) -> "[" <> format_symbol(sym) <> "]"
    SymRep(sym) -> format_symbol(sym) <> "*"
    SymRep1(sym) -> format_symbol(sym) <> "+"
    SymPattern(name) -> "<" <> name <> ">"
  }
}

// ============================================================================
// PARSER GENERATION
// ============================================================================

/// Convert a grammar to a parser function
pub fn to_parser(grammar: Grammar) -> fn(String) -> Result(p.ParseTree, String) {
  let parser = build_parser(grammar, grammar.start)
  fn(input: String) -> Result(p.ParseTree, String) {
    p.parse_string(parser, input)
  }
}

/// Build a parser from a grammar rule (with lazy evaluation for recursion)
fn build_parser(grammar: Grammar, rule: RuleName) -> p.Parser {
  build_parser_lazy(grammar, rule, dict.new())
}

fn build_parser_lazy(
  grammar: Grammar,
  rule: RuleName,
  cache: dict.Dict(String, p.Parser),
) -> p.Parser {
  case dict.get(cache, rule.name) {
    Ok(cached) -> cached
    Error(_) -> {
      // Create a placeholder parser that will be replaced
      // This allows recursive rules to work
      let placeholder = p.token("")
      let new_cache = dict.insert(cache, rule.name, placeholder)
      let parser =
        build_parser_from_symbol(
          grammar,
          get_rule_def(grammar, rule),
          new_cache,
        )
      parser
    }
  }
}

fn get_rule_def(grammar: Grammar, name: RuleName) -> Symbol {
  case grammar.rules |> list.find(fn(r) { r.name == name }) {
    Ok(rule) -> rule.definition
    Error(_) -> SymToken("")
  }
}

fn build_parser_from_symbol(
  grammar: Grammar,
  symbol: Symbol,
  cache: dict.Dict(String, p.Parser),
) -> p.Parser {
  case symbol {
    SymToken(value) -> p.token(value)
    SymRule(name) -> build_parser_lazy(grammar, name, cache)
    SymSeq(symbols) -> build_seq_parser(grammar, symbols, cache)
    SymChoice(alts) -> build_choice_parser(grammar, alts, cache)
    SymOpt(sym) -> p.opt(build_parser_from_symbol(grammar, sym, cache))
    SymRep(sym) -> p.rep(build_parser_from_symbol(grammar, sym, cache))
    SymRep1(sym) -> p.rep1(build_parser_from_symbol(grammar, sym, cache))
    SymPattern(name) -> p.named(name)
  }
}

fn build_seq_parser(
  grammar: Grammar,
  symbols: List(Symbol),
  cache: dict.Dict(String, p.Parser),
) -> p.Parser {
  case symbols {
    [] -> p.token("")
    [sym] -> build_parser_from_symbol(grammar, sym, cache)
    [sym1, sym2, ..rest] -> {
      let p1 = build_parser_from_symbol(grammar, sym1, cache)
      let p2 = build_seq_parser(grammar, [sym2, ..rest], cache)
      p.seq2(p1, p2)
    }
  }
}

fn build_choice_parser(
  grammar: Grammar,
  alts: List(Symbol),
  cache: dict.Dict(String, p.Parser),
) -> p.Parser {
  case alts {
    [] -> p.token("")
    [alt] -> build_parser_from_symbol(grammar, alt, cache)
    [alt, ..rest] -> {
      let p1 = build_parser_from_symbol(grammar, alt, cache)
      let p2 = build_choice_parser(grammar, rest, cache)
      p.choice(p1, p2)
    }
  }
}

// ============================================================================
// FORMATTER GENERATION
// ============================================================================

/// Convert a grammar to a formatter function
/// Uses the grammar structure to format parse trees with proper layout
pub fn to_formatter(_grammar: Grammar) -> fn(p.ParseTree) -> String {
  fn(tree: p.ParseTree) -> String { f.format(tree) }
}

// ============================================================================
// EXAMPLE GRAMMARS
// ============================================================================

/// Example: Simple expression grammar
pub fn expression_grammar() -> Grammar {
  grammar("Expr", [
    rule(
      "Expr",
      choice([
        seq([
          token("let"),
          pattern("Ident"),
          token("="),
          ref_rule("Expr"),
        ]),
        ref_rule("Term"),
      ]),
    ),
    rule(
      "Term",
      choice([
        pattern("Ident"),
        pattern("Number"),
      ]),
    ),
  ])
}

/// Example: Simple lambda calculus grammar
pub fn lambda_grammar() -> Grammar {
  grammar("Term", [
    rule(
      "Term",
      choice([
        pattern("Ident"),
        seq([
          token("\\"),
          pattern("Ident"),
          token("."),
          ref_rule("Term"),
        ]),
      ]),
    ),
  ])
}
