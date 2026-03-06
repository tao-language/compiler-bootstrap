// ============================================================================
// GRAMMAR - Language-Agnostic Grammar Definition
// ============================================================================
/// A declarative, language-agnostic grammar specification.
///
/// This module defines the structure of a formal grammar that can be used
/// to generate both parsers and formatters. The grammar is independent of
/// any specific language semantics.
///
/// # Example
///
/// ```gleam
/// let grammar = grammar.new()
///   |> grammar.rule("term", choice([rule("atom"), rule("lambda")]))
///   |> grammar.rule("atom", choice([term("ident"), term("number")]))
/// ```

import gleam/list
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// A grammar rule name
pub type RuleName {
  RuleName(name: String)
}

/// A terminal symbol (literal string to match)
pub type Terminal {
  Terminal(value: String)
}

/// A grammar symbol - the building blocks of rules
pub type Symbol {
  /// A literal terminal (e.g., "=>", "{", "}")
  SymTerminal(Terminal)
  /// A reference to another rule
  SymRule(RuleName)
  /// A sequence of symbols (all must match in order)
  SymSeq(List(Symbol))
  /// Alternative choices (first matching wins)
  SymChoice(List(Symbol))
  /// Optional symbol (may or may not match)
  SymOpt(Symbol)
  /// Zero or more repetitions (comma-separated)
  SymRep(Symbol)
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

/// Create a new empty grammar with the given start rule
pub fn new(start_rule: String) -> Grammar {
  Grammar([], RuleName(start_rule))
}

/// Add a rule to the grammar
pub fn rule(grammar: Grammar, name: String, definition: Symbol) -> Grammar {
  Grammar([Rule(RuleName(name), definition), ..grammar.rules], grammar.start)
}

/// Create a terminal symbol
pub fn term(value: String) -> Symbol {
  SymTerminal(Terminal(value))
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

/// Zero or more repetitions (comma-separated)
pub fn rep(symbol: Symbol) -> Symbol {
  SymRep(symbol)
}

// ============================================================================
// GRAMMAR INSPECTION
// ============================================================================

/// Get all rule names from a grammar
pub fn get_rule_names(grammar: Grammar) -> List(RuleName) {
  grammar.rules |> list.map(fn(rule) { rule.name })
}

/// Find a rule by name
pub fn find_rule(grammar: Grammar, name: RuleName) -> Result(Rule, Nil) {
  grammar.rules
  |> list.filter(fn(rule) { rule.name == name })
  |> list.first
}

/// Get the start rule name
pub fn get_start_rule(grammar: Grammar) -> RuleName {
  grammar.start
}

/// Format a grammar for debugging
pub fn format_grammar(grammar: Grammar) -> String {
  let rule_strings =
    grammar.rules
    |> list.map(fn(rule) {
      rule.name.name <> " -> " <> format_symbol(rule.definition)
    })
    |> string.join("\n")

  "Grammar(start: "
  <> grammar.start.name
  <> ")\n"
  <> rule_strings
}

/// Format a symbol for debugging
fn format_symbol(symbol: Symbol) -> String {
  case symbol {
    SymTerminal(Terminal(v)) -> "\"" <> v <> "\""
    SymRule(name) -> name.name
    SymSeq(symbols) ->
      symbols |> list.map(format_symbol) |> string.join(" ")
    SymChoice(alts) ->
      alts |> list.map(format_symbol) |> string.join(" | ")
    SymOpt(sym) -> "[" <> format_symbol(sym) <> "]"
    SymRep(sym) -> format_symbol(sym) <> "*"
  }
}
