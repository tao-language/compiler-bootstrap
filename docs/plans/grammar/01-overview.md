# Grammar System Overview

> **Goal**: Single source of truth for grammar that generates parsers with layout-aware formatting
> **Status**: ✅ Parser and formatter complete, ⏳ Source location tracking planned
> **Date**: March 2025

---

## Core Insight

A grammar rule should specify **what** to parse and **how** to format it. The grammar is the single source of truth for both parsing and formatting.

---

## Architecture

### Module Structure

```
src/syntax/
├── grammar.gleam    # Grammar DSL (~786 lines)
├── lexer.gleam      # Tokenizer (~400 lines)
└── formatter.gleam  # Document algebra (~139 lines)
```

### Data Flow

1. **Define Grammar**: Use `grammar.define()` DSL
2. **Parse Input**: `grammar.parse(grammar, source)` → AST
3. **Format AST**: Language-specific formatter using grammar metadata
4. **Round-trip**: parse → format → parse produces consistent output

---

## Design Principles

1. **Declarative**: Describe what the language looks like
2. **Type-Safe**: Grammar parameterized by AST type (`Grammar(a)`)
3. **Composable**: Build complex parsers from simple combinators
4. **Layout-Aware**: Soft/hard line breaks for pretty-printing
5. **Error Resilient**: Position tracking for error messages

---

## Implementation Status

### ✅ Complete and Working

**Lexer** (`src/syntax/lexer.gleam`):
- Tokenizes identifiers, keywords, numbers, strings
- Handles comments (line `//` and block `/* */`)
- Tracks positions for error reporting
- Supports Unicode (λ character)

**Grammar DSL** (`src/syntax/grammar.gleam`):
- `Grammar(a)` type parameterized by AST
- `Alternative` with constructor, deconstructor, formatter
- Pattern types: `TokenKind`, `Keyword`, `Ref`, `Seq`, `SeqWithLayout`, `Choice`, `Opt`, `Many`, `Sep1`, `Parens`
- Operator types with precedence, associativity, layout
- Builder API: `define`, `name`, `start`, `token`, `keyword`, `rule`, `left_assoc`, `right_assoc`
- Layout hints: `SoftBreak`, `HardBreak`, `Space`, `NoSeparator`
- Operator layouts: `default_op_layout`, `break_before_op_layout`

**Parser**:
- `parse_pattern()` - Dispatches on pattern type
- `parse_seq_with_layout()` - Parses sequences with hints
- `parse_left_assoc()` - Left-associative operator parsing
- `parse_right_assoc()` - Right-associative operator parsing
- Error handling with position tracking

**Formatter** (`src/syntax/formatter.gleam`):
- Document algebra: `Empty`, `Text`, `Line`, `HardLine`, `Group`, `Nest`, `Concat`
- `render()` - Best-fit rendering with configurable width
- `render_default()` - 80 character width
- Combinators: `space_sep`, `comma_sep`, `parens`, `braces`, `join`

**Examples**:
- Calculator (`src/examples/calc.gleam`) - Working example with +, -, *, /
- Supports precedence, associativity, parentheses
- Round-trip tested

### ⏳ In Progress / Pending

**Source Location Tracking** (9-14 hours estimated):
- [x] Update `Token` type to include `line` and `column`
- [x] Update lexer to store line/column in tokens
- [x] Add position helper functions to grammar DSL
- [x] Update `Span` type to support start/end positions
- [x] Update all grammar constructors to use real positions
- [x] Update tests for position tracking
- See **[05-source-location-tracking.md](./05-source-location-tracking.md)** for details

**Tests**:
- [x] Lexer tests (tokenization, position tracking) - 70 tests
- [x] Grammar DSL tests (pattern matching, operator precedence) - 37 tests  
- [x] Formatter tests (layout, line breaking) - 36 tests
- [x] Round-trip tests (parse → format → parse) - included in grammar tests

**Automatic Formatter Generation**:
- [ ] Implement deconstructor functions (currently panics)
- [ ] Grammar-derived formatting (currently manual)

**Core Language Grammar**:
- [ ] Define grammar for all Term variants
- [ ] Integrate with syntax library
- See **[../core/01-overview.md](../core/01-overview.md)** for status

**Error Recovery**:
- [ ] Sync-point recovery for better error messages
- [ ] Multiple error reporting (don't stop at first error)

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

### 2. Bidirectional Alternatives

Each alternative has constructor (parse) and formatter (format):

```gleam
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,      // Parse: values → AST
    deconstructor: fn(a) -> List(Value(a)),    // Format: AST → values (TODO)
    formatter: fn(a, Int) -> Doc,              // Format: AST → Doc
  )
}
```

### 3. Layout Configuration

Grammar stores formatting metadata:

```gleam
pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    break_before: Bool,
    break_after: Bool,
    indent_rhs: Bool,
  )
}

pub fn default_op_layout(separator: String) -> OperatorLayout {
  OperatorLayout(
    separator: separator,
    break_before: False,
    break_after: True,   // Break after operator
    indent_rhs: True,    // Indent RHS when broken
  )
}
```

---

## Example: Calculator Grammar

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.token("LParen")
  |> grammar.token("RParen")
  |> grammar.left_assoc(
    "Expr", "Term",
    [
      grammar.op("+", Add, 10, grammar.default_op_layout("+")),
      grammar.op("-", Sub, 10, grammar.default_op_layout("-")),
    ],
    10,
  )
  |> grammar.left_assoc(
    "Term", "Factor",
    [
      grammar.op("*", Mul, 20, grammar.default_op_layout("*")),
      grammar.op("/", Div, 20, grammar.default_op_layout("/")),
    ],
    20,
  )
  |> grammar.rule("Factor", [
    grammar.alt(
      grammar.token_pattern("Number"),
      fn(values) { Int(int.parse(token.value) |> result.unwrap(0)) },
      fn(ast, _) { formatter.text(int.to_string(n)) },
    ),
    grammar.alt(
      grammar.parenthesized("Expr"),
      fn(values) { expr },
      fn(ast, prec) { format_expr(ast, prec) },
    ),
  ])
}
```

---

## Related Documents

- **[02-grammar-dsl.md](./02-grammar-dsl.md)** - Grammar DSL specification
- **[03-parser-library.md](./03-parser-library.md)** - Parser combinator library
- **[04-formatter-library.md](./04-formatter-library.md)** - Formatter library with layout
- **[../syntax-library.md](../../syntax-library.md)** - Final user-facing documentation

---

## References

- [Grammar Implementation](../../src/syntax/grammar.gleam)
- [Lexer Implementation](../../src/syntax/lexer.gleam)
- [Formatter Implementation](../../src/syntax/formatter.gleam)
- [Calc Example](../../src/examples/calc.gleam)
