# Grammar System Overview

> **Goal**: Single source of truth for grammar that automatically generates both parser and formatter
> **Status**: ✅ Parser complete, ⏳ Automatic formatter generation in progress
> **Date**: March 2025

---

## Core Insight

A grammar rule should specify **what** to parse and **how** to format it, not **how** to parse it. The system should handle the mechanics automatically.

```
Grammar (single source of truth)
    ├── Parser (automatically generated) ✅
    └── Formatter (automatically generated) ⏳
```

---

## Architecture

### Module Structure

```
src/
├── grammar.gleam         # Grammar DSL and generation
├── parser.gleam          # Parser combinators + Pratt parsing
├── formatter.gleam       # Document algebra pretty printer
└── lexer.gleam           # Generic tokenizer
```

### Data Flow

1. **Define Grammar**: Use `grammar.gleam` DSL
2. **Generate Parser**: `grammar.to_parser(grammar)` 
3. **Parse Input**: Parser produces `ParseTree` or AST
4. **Generate Formatter**: `grammar.to_formatter(grammar)`
5. **Format Output**: Formatter produces formatted string

---

## Design Principles

1. **Declarative**: Describe what the language looks like, not how to parse it
2. **Type-Safe**: Grammar parameterized by AST type
3. **Composable**: Build complex grammars from simple rules
4. **Minimal Boilerplate**: Maximum automation, flexibility where needed
5. **Error Resilient**: Accumulate errors, never stop on first error

---

## Current Implementation Status

### ✅ Working (Parser)

- Lexer tokenizes numbers, identifiers, operators, parentheses, strings, comments
- Grammar DSL with declarative builder pattern
- Parser handles all patterns (Token, Keyword, Op, Ref, Seq, Choice, Opt, Many, Sep1, Parens)
- Left-associative operator parsing with correct folding
- Operator precedence handling
- Parenthesized expressions
- **238 tests passing**

### ⏳ In Progress (Formatter)

- Manual formatter implemented for calc example
- Precedence-based parenthesization working correctly
- Round-trip tests passing (parse → format → parse)
- **Automatic formatter generation from grammar** - needs implementation

---

## Key Concepts

### 1. Precedence-Based Parenthesization

For left-associative operators:
- **Left operand**: same precedence (no parens for same level)
- **Right operand**: precedence + 1 (parens for same level)

```gleam
Add(l, r) ->
  format_binop(
    format_expr(l, 10),   // Left: same prec
    format_expr(r, 11),   // Right: prec + 1
    " + ",
    10,                   // Operator precedence
    parent_prec,
  )
```

This ensures:
- `1 + 2 + 3` → `1 + 2 + 3` (not `(1 + 2) + 3`)
- `1 + 2 * 3` → `1 + 2 * 3` (correct precedence)
- `(1 + 2) * 3` → `(1 + 2) * 3` (parens preserved when needed)

### 2. Bidirectional Operators

Operators need both constructor (parsing) and deconstructor (formatting):

```gleam
pub type Operator(a) {
  Operator(
    keyword: String,
    constructor: fn(a, a) -> a,      // For parsing: (left, right) -> AST
    deconstructor: fn(a) -> #(a, a), // For formatting: AST -> (left, right)
    precedence: Int,
    associativity: Associativity,
    layout: LayoutStyle,
  )
}
```

### 3. Layout Configuration

Grammar stores formatting metadata:

```gleam
pub type LayoutStyle {
  Inline
  BreakAfterOperator(indent: Int)
  BreakBeforeOperator(indent: Int)
  Block(open: String, close: String, indent: Int)
}
```

---

## Example: Calculator Grammar

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10),
    grammar.op("-", Sub, 10),
  ])
  |> grammar.left_assoc("Term", "Factor", [
    grammar.op("*", Mul, 20),
    grammar.op("/", Div, 20),
  ])
  |> grammar.rule("Factor", [
    grammar.alt(grammar.int_token("Number"), fn(n) { Int(n) }),
    grammar.alt(grammar.parens("Expr"), fn(e) { e }),
  ])
}

// Usage:
let grammar = calc_grammar()
let result = grammar.parse(grammar, "1 + 2 * 3")
let source = grammar.format(grammar, result.ast)
// source = "1 + 2 * 3" (correct precedence, no extra parens!)
```

---

## Related Documents

- **[02-grammar-dsl.md](./02-grammar-dsl.md)** - Grammar DSL specification
- **[03-parser-library.md](./03-parser-library.md)** - Parser combinator library
- **[04-formatter-library.md](./04-formatter-library.md)** - Formatter library with layout

---

## References

- [Current Implementation](../../src/syntax/grammar.gleam)
- [Calc Example](../../src/examples/calc.gleam)
- [Core Language Specification](../core.md)
