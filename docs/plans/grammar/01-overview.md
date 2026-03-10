# Grammar System Overview

> **Goal**: Single source of truth for grammar that generates parsers with layout-aware formatting
> **Status**: ✅ Complete and tested (263 tests passing)
> **Date**: March 2025

---

## Core Insight

A grammar rule should specify **what** to parse and **how** to format it. The grammar is the single source of truth for both parsing and formatting.

---

## Architecture

### Module Structure

```
src/syntax/
├── grammar.gleam    # Grammar DSL (~786 lines) ✅
├── lexer.gleam      # Tokenizer (~400 lines) ✅
└── formatter.gleam  # Document algebra (~139 lines) ✅
```

### Data Flow

1. **Define Grammar**: Use `grammar.define()` DSL
2. **Parse Input**: `grammar.parse(grammar, source)` → AST + errors
3. **Format AST**: Language-specific formatter using grammar metadata
4. **Round-trip**: parse → format → parse produces consistent output

---

## Design Principles

1. **Declarative**: Describe what the language looks like
2. **Type-Safe**: Grammar parameterized by AST type (`Grammar(a)`)
3. **Composable**: Build complex parsers from simple combinators
4. **Layout-Aware**: Soft/hard line breaks for pretty-printing
5. **Error Resilient**: Position tracking for error messages, never panics

---

## Implementation Status

### ✅ Complete and Working

**Lexer** (`src/syntax/lexer.gleam` ~400 lines):
- Tokenizes identifiers, keywords, numbers, strings, operators
- Handles comments (line `//` and block `/* */`)
- Full source location tracking (line, column, start, end offsets)
- Supports Unicode (λ character)
- **70 tests passing**

**Grammar DSL** (`src/syntax/grammar.gleam` ~786 lines):
- `Grammar(a)` type parameterized by AST
- `Alternative` with constructor, deconstructor (stub), formatter
- Pattern types: `TokenKind`, `Keyword`, `Ref`, `Seq`, `SeqWithLayout`, `Choice`, `Opt`, `Many`, `Sep1`, `Parens`
- Operator types with precedence, associativity, layout
- Builder API: `define`, `name`, `start`, `token`, `keyword`, `rule`, `left_assoc`, `right_assoc`
- Layout hints: `SoftBreak`, `HardBreak`, `Space`, `NoSeparator`
- Operator layouts: `default_op_layout`, `break_before_op_layout`
- Position helpers: `span_from_values`, `span_from_token`, `span_from_tokens`
- **37 tests passing**

**Parser** (integrated in `grammar.gleam`):
- `parse_pattern()` - Dispatches on pattern type
- `parse_seq_with_layout()` - Parses sequences with hints
- `parse_left_assoc()` - Left-associative operator parsing
- `parse_right_assoc()` - Right-associative operator parsing
- `fold_operators_multi()` - Fold multiple operators
- Error handling with position tracking
- `ParseResult` with ast and errors list (never panics)
- **Integrated with lexer and grammar DSL**

**Formatter** (`src/syntax/formatter.gleam` ~139 lines):
- Document algebra: `Empty`, `Text`, `Line`, `HardLine`, `Group`, `Nest`, `Concat`
- `render()` - Best-fit rendering with configurable width
- `render_default()` - 80 character width
- Combinators: `space_sep`, `comma_sep`, `parens`, `braces`, `join`
- Layout hints: `SoftBreak`, `HardBreak`, `Space`, `None`
- Operator layout: `OperatorLayout` with `break_before`, `break_after`, `indent_rhs`
- Precedence-based parenthesization
- **36 tests passing**

**Examples**:
- Calculator (`src/examples/calc.gleam`) - Working example with +, -, *, /
- Supports precedence, associativity, parentheses
- Round-trip tested (parse → format → parse)

**Source Location Tracking** (`src/syntax/lexer.gleam`, `src/core/core.gleam`):
- ✅ Token type includes `line` and `column`
- ✅ Lexer stores line/column in all tokens
- ✅ Position helper functions in grammar DSL
- ✅ Span type supports start/end positions (line/column)
- ✅ All grammar constructors use real positions
- ✅ All tests updated and passing
- See **[05-source-location-tracking.md](./05-source-location-tracking.md)** for details

**Total: 263 tests passing** (70 lexer + 37 grammar + 36 formatter + 120 core language tests)

### ⏳ In Progress / Pending

**Grammar Library Enhancements**:
- [ ] **Sum type layout** - Add `SumType(indent, pipe_on_each)` layout style for multi-line sum types
  - Example: `type Maybe(a) = | Some(a) | None`
  - Estimated effort: ~50 lines
  - **Required for**: Tao sum type definitions
- [ ] **Semicolon inference** - Add `NewlineSep` layout hint for statement separation
  - Example: `do { let x = 1; let y = 2; x + y }`
  - Estimated effort: ~100 lines
  - **Required for**: Tao imperative blocks

**Automatic Formatter Generation**:
- ❌ **Full automation NOT feasible** - See [06-automatic-formatter-analysis.md](./06-automatic-formatter-analysis.md)
- ✅ **Grammar-derived metadata FEASIBLE** - See [08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)
- [ ] Implement metadata generation (1-2 days)
- [ ] Implement metadata-aware combinators (1 day)
- [ ] Update examples to use new approach (1 day)

See **[06-automatic-formatter-analysis.md](./06-automatic-formatter-analysis.md)** for why full automation is not feasible.
See **[08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)** for grammar-derived metadata approach.

**Recommended Approach**:

1. **Generate metadata from grammar** - Precedence table, layout hints
2. **Single manual format function** - Pattern match once, use combinators
3. **Combinators lookup metadata** - No precedence duplication
4. **Exhaustiveness checking** - Compiler verifies all cases covered

**Benefits**:
- Precedence defined ONCE in grammar (zero duplication)
- Layout hints from grammar (zero duplication)
- Full control over formatting (manual pattern match)
- Automatic pretty-printing (soft/hard breaks, multiple strategies)

**Core Language Grammar**:
- [ ] Define grammar for all Term variants (Var, Lam, App, Pi, Rcd, Match, Ctr, Hole, Lit, Ann, Call, Comptime)
- [ ] Integrate with syntax library
- [ ] See **[../core/01-overview.md](../core/01-overview.md)** for status
- [ ] See **[../core/04-tao-integration.md](../core/04-tao-integration.md)** for Tao integration requirements

**Error Recovery**:
- [ ] Sync-point recovery for better error messages
- [ ] Multiple error reporting (currently accumulates but could be improved)
- [ ] Rule-specific error messages (currently generic "expected X")

**Documentation**:
- [ ] User-facing syntax library documentation (`docs/syntax-library.md` draft exists)
- [ ] More examples beyond calculator

### 📋 Tao Language Grammar Plan

The Tao language grammar will be implemented in three phases:

**Phase 1: Lexer** (`src/tao/lexer.gleam`):
- Base on existing `syntax/lexer.gleam`
- Add Tao-specific tokens (IntLit, FloatLit, StringLit, UpperIdent)
- Handle keywords (let, mut, fn, type, match, if, import, etc.)
- Track positions for error reporting
- Estimated effort: ~400 lines, 50+ tests

**Phase 2: Grammar Definition** (`src/tao/grammar.gleam`):
- Define all grammar rules using syntax library DSL
- Set up 10 operator precedence levels
- Handle sum type layout (requires grammar library enhancement)
- Handle pattern matching syntax (OCaml style with `|`)
- Handle module syntax (import, as, names)
- Estimated effort: ~600 lines, 30+ tests

**Phase 3: Parser** (`src/tao/parser.gleam`):
- Thin wrapper around syntax library parser
- Error handling and reporting
- Source location tracking
- Estimated effort: ~100 lines, 20+ tests

**Total estimated effort**: ~1100 lines, 100+ tests, 2-3 weeks

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
