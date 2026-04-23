# Syntax Library Overview

> **Goal**: Single source of truth for grammar that generates parsers with layout-aware formatting and error reporting
> **Status**: ✅ Complete and tested (519 tests passing)
> **Date**: March 2025 (Updated: March 2026 - Post reorganization)

---

## Core Insight

The grammar is the **single source of truth** for parsing. Formatters are separate but can extract metadata (precedence, layout) from the grammar to avoid duplication.

---

## Architecture

### Module Structure

```
src/syntax/
├── grammar.gleam         # Grammar DSL (~1100 lines) ✅
├── lexer.gleam           # Tokenizer (~400 lines) ✅
├── formatter.gleam       # Document algebra (~440 lines) ✅
├── source_snippet.gleam  # Source snippet formatter (~260 lines) ✅
└── error_reporter.gleam  # Error to diagnostic conversion (~220 lines) ✅
```

### Data Flow

1. **Define Grammar**: Direct record construction `Grammar(...)`
2. **Parse Input**: `grammar.parse(grammar, source, error_ast)` → AST + errors
3. **Format AST**: Language-specific formatter (can extract metadata from grammar)
4. **Report Errors**: Convert errors to diagnostics with source snippets
5. **Round-trip**: parse → format → parse produces consistent output

---

## Design Principles

1. **Declarative**: Describe what the language looks like
2. **Type-Safe**: Grammar parameterized by AST type (`Grammar(a)`)
3. **Composable**: Build complex parsers from simple combinators
4. **Layout-Aware**: Soft/hard line breaks for pretty-printing
5. **Error Resilient**: Position tracking for error messages, never panics
6. **Actionable Errors**: Clear hints and suggestions for fixing errors
7. **Source Locations**: Full span tracking from tokens to AST

---

## Implementation Status

### ✅ Complete and Working (v2.0)

**Lexer** (`src/syntax/lexer.gleam` ~400 lines):
- Tokenizes identifiers, keywords, numbers, strings, operators
- Handles comments (line `//` and block `/* */`)
- Full source location tracking (line, column, start, end offsets)
- Supports Unicode (λ character)
- **70 tests passing**

**Grammar DSL** (`src/syntax/grammar.gleam` ~1100 lines):
- `Grammar(a)` type parameterized by AST (direct record construction)
- `Alternative` with constructor only (no deconstructor/formatter stubs)
- Pattern types: `TokenKind`, `Keyword`, `Ref`, `Seq`, `SeqWithLayout`, `Choice`, `Opt`, `Many`, `Sep1`, `Parens`
- **Operator types**: `OperatorKind` (4 kinds), `PostfixPattern` (recursive), `Operator` (sum type)
- **Operator helpers**: `prefix()`, `postfix()`, `infix_binary()`, `infix_wrapped()`, `infix_ternary()`, `infix_slice()`
- **Query API**: `get_operator()`, `get_operator_precedence()`, `get_operator_kind()`
- Layout hints: `SoftBreak`, `HardBreak`, `Space`, `NoSeparator`
- **Metadata extraction**: `extract_precedence_table`, `extract_layout_table` (deprecated)
- **Grammar-based formatting**: `format_binop_with_grammar`
- **Span tracking**: Spans propagated from tokens through parsing
- **All tests passing**

**Parser** (integrated in `grammar.gleam`):
- `parse_pattern()` - Dispatches on pattern type
- `parse_seq_with_layout()` - Parses sequences with hints
- `parse_left_assoc()` - Left-associative operator parsing
- `parse_right_assoc()` - Right-associative operator parsing
- `fold_operators_multi()` - Fold multiple operators
- Error handling with position tracking
- `ParseResult` with ast and errors list (never panics)
- **Integrated with lexer and grammar DSL**

**Formatter** (`src/syntax/formatter.gleam` ~440 lines):
- Document algebra: `Empty`, `Text`, `Line`, `HardLine`, `Group`, `Nest`, `Concat`
- `render()` - Best-fit rendering with configurable width
- `render_default()` - 80 character width
- Combinators: `space_sep`, `comma_sep`, `parens`, `braces`, `join`
- Precedence-based parenthesization
- **16+ combinators**: `format_binop_auto`, `format_unary`, `format_wrapped`, `format_list`, `format_application`, `format_lambda`, `format_record`, `format_record_auto`, `format_match`, `format_case`, `format_inline`, `format_soft_break`, `format_hard_break`
- **All tests passing**

**Source Snippet** (`src/syntax/source_snippet.gleam` ~260 lines):
- Diagnostic type with code, severity, message, spans, notes, hints
- Source snippet formatting with line numbers and pointers
- Multi-span error support (type mismatches)
- Pretty-printing with colors (future)
- **Integrated with error reporter**

**Error Reporter** (`src/syntax/error_reporter.gleam` ~220 lines):
- Parse error to diagnostic conversion
- Type error to diagnostic conversion
- Error codes (E0001, E0101-E0106, E0201-E0202, E0301)
- Hints for all error types
- **Integrated with CLI**

**Examples**:
- Calculator (`src/syntax/examples/calc.gleam`) - Working example with +, -, *, /
- Supports precedence, associativity, parentheses
- Round-trip tested (parse → format → parse)
- Uses grammar-derived formatter with metadata-aware combinators
- **Full span tracking** for error reporting
- **All tests passing**

**Total: 358 tests passing**

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
- [ ] Implement metadata generation CLI command (optional, deferred)

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
- ✅ User-facing syntax library documentation (`docs/syntax-library.md`)
- [ ] More examples beyond calculator

---

## Key Components

### Grammar DSL

The grammar DSL allows you to define parsers declaratively:

```gleam
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.left_assoc("Expr", "Term", [
    grammar.op("+", Add, 10, grammar.default_op_layout("+")),
    grammar.op("-", Sub, 10, grammar.default_op_layout("-")),
  ], 10)
}
```

### Formatter Combinators

16+ combinators reduce formatter boilerplate by 70-80%:

```gleam
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  case ast {
    Add(l, r) ->
      format_binop_auto(
        format_expr,  // Recursive formatter
        l,
        r,
        "+",   // Operator separator
        10,    // Precedence from grammar
        parent_prec,
      )
  }
}
```

### Error Reporting

Convert errors to diagnostics with source snippets:

```gleam
let diagnostic = error_reporter.parse_error_to_diagnostic(error, source, file)
source_snippet.format_diagnostic(diagnostic, source)
```

Output:
```
error[E0001]: Unexpected token
   ┌─ src/file.gleam:3:5
   │
 3 │ 1 + * 3
   │     ^
   │
   = Expected: expression
   = Got: *
```

---

## Related Documents

- **[02-grammar-dsl.md](./02-grammar-dsl.md)** - Grammar DSL specification
- **[03-parser-library.md](./03-parser-library.md)** - Parser implementation
- **[04-formatter-library.md](./04-formatter-library.md)** - Formatter implementation
- **[05-source-location-tracking.md](./05-source-location-tracking.md)** - Source location tracking
- **[06-automatic-formatter-analysis.md](./06-automatic-formatter-analysis.md)** - Why full automation not feasible
- **[08-grammar-derived-formatter-plan.md](./08-grammar-derived-formatter-plan.md)** - Grammar-derived formatter (COMPLETE)
- **[../../docs/syntax-library.md](../../docs/syntax-library.md)** - Complete syntax library documentation
- **[../../docs/cli.md](../../docs/cli.md)** - CLI documentation

---

## References

- [Grammar Implementation](../../src/syntax/grammar.gleam)
- [Lexer Implementation](../../src/syntax/lexer.gleam)
- [Formatter Implementation](../../src/syntax/formatter.gleam)
- [Source Snippet](../../src/syntax/source_snippet.gleam)
- [Error Reporter](../../src/syntax/error_reporter.gleam)
- [Calculator Example](../../src/examples/calc.gleam)
