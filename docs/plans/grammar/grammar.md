# Grammar, Parser, and Formatter Documentation

This document explains the unified grammar system and the underlying parser and formatter libraries.

---

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Grammar DSL](#grammar-dsl)
4. [Parser Library](#parser-library)
5. [Formatter Library](#formatter-library)
6. [Example Grammars](#example-grammars)
7. [API Reference](#api-reference)

---

## Overview

The grammar system provides a **single source of truth** for language syntax. You define a grammar once and the system automatically generates both parsers and formatters.

```
grammar.gleam (Grammar DSL)
     ↓
   ┌─┴─┐
   ↓   ↓
parser.gleam  formatter.gleam
   ↓           ↓
ParseTree   String
```

### Benefits

- **Consistency**: Parser and formatter always agree on syntax
- **Maintainability**: Change syntax in one place
- **Simplicity**: No duplicate parser/formatter logic

### Modules

| Module | Purpose |
|--------|---------|
| `grammar.gleam` | Grammar DSL and grammar-to-parser/formatter generation |
| `parser.gleam` | General-purpose parser combinators producing ParseTree |
| `formatter.gleam` | Grammar-aware tree formatter with layout |

### Usage

```gleam
import grammar

// Define grammar
let g = grammar.grammar("Expr", [
  grammar.rule("Expr", grammar.choice([
    grammar.seq([
      grammar.token("let"),
      grammar.pattern("Ident"),
      grammar.token("="),
      grammar.ref("Expr"),
    ]),
    grammar.ref("Term"),
  ])),
  grammar.rule("Term", grammar.choice([
    grammar.pattern("Ident"),
    grammar.pattern("Number"),
  ])),
])

// Generate parser
let parse = grammar.to_parser(g)

// Generate formatter
let format = grammar.to_formatter(g)

// Use them
let result = parse("let x = 42")
case result {
  Ok(tree) -> format(tree) // Returns formatted string
  Error(e) -> // Handle error
}
```

---

## Architecture

### Module Structure

```
src/
├── grammar.gleam         (~320 lines)
│   ├── Grammar DSL types
│   ├── Grammar builders
│   └── to_parser/to_formatter
├── parser.gleam          (~190 lines)
│   └── Parser combinators producing ParseTree
└── formatter.gleam       (~200 lines)
    └── Tree formatter with grammar-aware layout
```

### Data Flow

1. **Define Grammar**: Use `grammar.gleam` DSL
2. **Generate Parser**: `grammar.to_parser(grammar)` returns `fn(String) -> Result(ParseTree, String)`
3. **Parse Input**: Parser produces `ParseTree`
4. **Generate Formatter**: `grammar.to_formatter(grammar)` returns `fn(ParseTree) -> String`
5. **Format Output**: Formatter produces formatted string with proper layout

---

## Grammar DSL

The grammar DSL provides functions for defining grammar rules.

### Basic Grammar Structure

```gleam
import grammar

let my_grammar = grammar.grammar("StartRule", [
  grammar.rule("StartRule", grammar.choice([
    grammar.seq([
      grammar.token("keyword"),
      grammar.ref("Expression"),
    ]),
    grammar.ref("Expression"),
  ])),
  grammar.rule("Expression", grammar.choice([
    grammar.pattern("Ident"),
    grammar.pattern("Number"),
  ])),
])
```

### Grammar Combinators

| Function | Description | Example |
|----------|-------------|---------|
| `grammar(start, rules)` | Create a grammar | `grammar("Expr", [rule1, rule2])` |
| `rule(name, definition)` | Define a rule | `rule("Expr", seq([...]))` |
| `token(value)` | Match literal token | `token("let")` |
| `ref(name)` | Reference another rule | `ref("Expr")` |
| `seq([symbols])` | Sequence (all must match) | `seq([token("x"), ref("Y")])` |
| `choice([alternatives])` | Choice (first match wins) | `choice([rule1, rule2])` |
| `opt(symbol)` | Optional (0 or 1) | `opt(token(";"))` |
| `rep(symbol)` | Repetition (0 or more) | `rep(seq([token(","), ref("Item")]))` |
| `rep1(symbol)` | Repetition (1 or more) | `rep1(ref("Item"))` |
| `pattern(name)` | Named pattern (captures token) | `pattern("Ident")` |

### Terminal Symbols

Terminals are literal strings to match:

```gleam
// Keywords
grammar.token("let")
grammar.token("if")
grammar.token("else")

// Operators
grammar.token("+")
grammar.token("=>")
grammar.token("=")

// Delimiters
grammar.token("(")
grammar.token("{")
grammar.token("[")
```

### Non-Terminal Symbols

Non-terminals reference other rules:

```gleam
grammar.ref("Expression")
grammar.ref("Statement")
grammar.ref("Type")
```

### Patterns

Patterns capture tokens for use in formatting:

```gleam
grammar.pattern("Ident")    // Identifier
grammar.pattern("Number")   // Number literal
grammar.pattern("String")   // String literal
```

---

## Parser Library

The parser library (`parser.gleam`) provides general-purpose parser combinators that produce parse trees.

### Parse Tree Type

```gleam
pub type ParseTree {
  /// A token leaf
  TreeToken(String)
  /// A named node with children
  TreeNode(name: String, children: List(ParseTree))
}
```

### Basic Parsers

```gleam
/// Parse a specific token
pub fn token(value: String) -> Parser

/// Parse and capture any token as a named node
pub fn named(name: String) -> Parser

/// Parse and capture any token
pub fn any_token() -> Parser
```

### Combinators

```gleam
/// Sequence: parse p1 then p2
pub fn seq2(p1: Parser, p2: Parser) -> Parser

/// Sequence three parsers
pub fn seq3(p1: Parser, p2: Parser, p3: Parser) -> Parser

/// Choice: try p1, if fails try p2
pub fn choice(p1: Parser, p2: Parser) -> Parser

/// Optional: parse or succeed with empty
pub fn opt(p: Parser) -> Parser

/// Zero or more repetitions
pub fn rep(p: Parser) -> Parser

/// One or more repetitions
pub fn rep1(p: Parser) -> Parser

/// Map parser result
pub fn map(p: Parser, f: fn(ParseTree) -> ParseTree) -> Parser
```

### Running Parsers

```gleam
/// Run a parser on a string input
pub fn parse_string(parser: Parser, input: String) -> Result(ParseTree, String)
```

### Example

```gleam
import parser

// Parse "hello world"
let p = parser.seq2(parser.token("hello"), parser.token("world"))
case parser.parse_string(p, "hello world") {
  Ok(TreeNode("Seq", [TreeToken("hello"), TreeToken("world")])) -> // Success
  Error(e) -> // Error
}
```

---

## Formatter Library

The formatter library (`formatter.gleam`) provides grammar-aware tree formatting with proper layout.

### Basic Formatters

```gleam
/// Format a token (leaf node)
pub fn format_token(tree: ParseTree, ctx: FormatContext) -> String

/// Format a node with children on same line
pub fn format_inline(tree: ParseTree, ctx: FormatContext) -> String

/// Format a node with children on separate lines (indented)
pub fn format_block(tree: ParseTree, ctx: FormatContext) -> String
```

### Grammar-Aware Formatting

```gleam
/// Format a parse tree using grammar-aware formatting
pub fn format(tree: ParseTree) -> String

/// Format with custom context
pub fn format_with_context(tree: ParseTree, ctx: FormatContext) -> String
```

### Formatting Context

```gleam
/// Create a new format context
pub fn new_context() -> FormatContext

/// Create context with custom indent
pub fn with_indent(indent_string: String) -> FormatContext

/// Increase indentation level
pub fn indent(ctx: FormatContext) -> FormatContext
```

### Example Output

For input `let x = 42`:
- Parse tree: `TreeNode("Start", [...])`
- Formatted: `"let x = 42"`

For lambda `\x. y`:
- Parse tree: `TreeNode("Term", [...])`
- Formatted: `"\x. y"`

---

## Example Grammars

### Simple Expressions

```gleam
pub fn expression_grammar() -> grammar.Grammar {
  grammar.grammar("Expr", [
    grammar.rule("Expr", grammar.choice([
      // let x = expr
      grammar.seq([
        grammar.token("let"),
        grammar.pattern("Ident"),
        grammar.token("="),
        grammar.ref("Expr"),
      ]),
      // term
      grammar.ref("Term"),
    ])),
    
    grammar.rule("Term", grammar.choice([
      grammar.pattern("Ident"),
      grammar.pattern("Number"),
    ])),
  ])
}
```

### Lambda Calculus

```gleam
pub fn lambda_grammar() -> grammar.Grammar {
  grammar.grammar("Term", [
    grammar.rule("Term", grammar.choice([
      // Variable
      grammar.pattern("Ident"),
      // Lambda: \x. term
      grammar.seq([
        grammar.token("\\"),
        grammar.pattern("Ident"),
        grammar.token("."),
        grammar.ref("Term"),
      ]),
    ])),
  ])
}
```

---

## API Reference

### Grammar Construction (`grammar.gleam`)

```gleam
/// Create a new grammar with a start rule
pub fn grammar(start: String, rules: List(Rule)) -> Grammar

/// Create a grammar rule
pub fn rule(name: String, definition: Symbol) -> Rule

/// Create a terminal symbol
pub fn token(value: String) -> Symbol

/// Create a rule reference
pub fn ref(name: String) -> Symbol

/// Create a sequence of symbols
pub fn seq(symbols: List(Symbol)) -> Symbol

/// Create a choice between alternatives
pub fn choice(alternatives: List(Symbol)) -> Symbol

/// Make a symbol optional
pub fn opt(symbol: Symbol) -> Symbol

/// Zero or more repetitions
pub fn rep(symbol: Symbol) -> Symbol

/// One or more repetitions
pub fn rep1(symbol: Symbol) -> Symbol

/// Create a named pattern (for capturing tokens)
pub fn pattern(name: String) -> Symbol

/// Convert a grammar to a parser function
pub fn to_parser(grammar: Grammar) -> fn(String) -> Result(ParseTree, String)

/// Convert a grammar to a formatter function
pub fn to_formatter(grammar: Grammar) -> fn(ParseTree) -> String
```

### Parser Combinators (`parser.gleam`)

```gleam
/// Parse a specific token
pub fn token(value: String) -> Parser

/// Parse and capture any token as a named node
pub fn named(name: String) -> Parser

/// Parse and capture any token
pub fn any_token() -> Parser

/// Sequence: parse p1 then p2
pub fn seq2(p1: Parser, p2: Parser) -> Parser

/// Choice: try p1, if fails try p2
pub fn choice(p1: Parser, p2: Parser) -> Parser

/// Optional: parse or succeed with empty
pub fn opt(p: Parser) -> Parser

/// Zero or more repetitions
pub fn rep(p: Parser) -> Parser

/// One or more repetitions
pub fn rep1(p: Parser) -> Parser

/// Map parser result
pub fn map(p: Parser, f: fn(ParseTree) -> ParseTree) -> Parser

/// Run a parser on a string input
pub fn parse_string(parser: Parser, input: String) -> Result(ParseTree, String)
```

### Formatter Combinators (`formatter.gleam`)

```gleam
/// Format a token (leaf node)
pub fn format_token(tree: ParseTree, ctx: FormatContext) -> String

/// Format a node with children on same line
pub fn format_inline(tree: ParseTree, ctx: FormatContext) -> String

/// Format a node with children on separate lines (indented)
pub fn format_block(tree: ParseTree, ctx: FormatContext) -> String

/// Format a parse tree using grammar-aware formatting
pub fn format(tree: ParseTree) -> String

/// Format with custom context
pub fn format_with_context(tree: ParseTree, ctx: FormatContext) -> String

/// Create a new format context
pub fn new_context() -> FormatContext

/// Create context with custom indent
pub fn with_indent(indent_string: String) -> FormatContext

/// Increase indentation level
pub fn indent(ctx: FormatContext) -> FormatContext
```

---

## Testing

### Running Tests

```bash
gleam test
```

### Test Files

- `test/grammar_test.gleam` - Grammar DSL and integration tests
- `test/parser_test.gleam` - Parser combinator tests
- `test/formatter_test.gleam` - Formatter combinator tests

---

## Limitations

### Recursive Grammars

The current implementation has limited support for recursive grammars. Recursive rules (like `Expr -> ( Expr )`) may cause infinite loops during parser construction. A more sophisticated lazy evaluation mechanism is needed for full recursive grammar support.

### Formatter

The current formatter provides basic grammar-aware formatting. Advanced features like:
- Custom formatting rules per grammar rule
- Configurable output styles
- Advanced layout algorithms

would require extending the formatter with rule-specific formatting functions.

---

## See Also

- [Core Language Specification](core.md) - The core language grammar
