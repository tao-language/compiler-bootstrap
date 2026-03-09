# Core Language Overview

> **Status**: ✅ Complete and tested (263 tests), ⏳ Tao integration planned
> **Date**: March 2025

---

## Core Principle

**The grammar is the single source of truth.** It defines:
1. What to parse (patterns)
2. How to construct AST from parsed values (constructors)
3. How to format values back to source (formatters)

Both parser and formatter are **derived from the same grammar definition**.

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     Core Language Syntax                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  src/core/syntax.gleam (single source of truth)                 │
│  ├── core_grammar() - Grammar definition                         │
│  ├── parse() - Parser (generated from grammar)                  │
│  └── format() - Formatter (generated from grammar)              │
│                                                                  │
│  Grammar → Parser + Formatter                                    │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │  grammar.alt(pattern, constructor, formatter)            │   │
│  │  - pattern: what to match                                │   │
│  │  - constructor: values → AST                             │   │
│  │  - formatter: AST → Doc                                  │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Design Principles

1. **Single file** - `src/core/syntax.gleam` contains grammar, constructors, and formatters
2. **Grammar-derived** - Both parser and formatter generated from grammar
3. **TypeScript-like syntax** - Familiar to web developers
4. **C-style application only** - `f(x, y)` not `f x y`
5. **De Bruijn indices** - Internal representation uses indices, not names

---

## Implementation Status

### ✅ Complete and Working

**Syntax Library** (`src/syntax/`):
- Lexer - Tokenizes identifiers, keywords, numbers, strings, comments
- Grammar DSL - Full layout-aware grammar definition with `Alternative` type
- Formatter - Document algebra with best-fit rendering
- Calculator example - Working parser/formatter with +, -, *, /
- **263 tests passing**

**Core Language** (`src/core/core.gleam`):
- `Term` types - All 13 constructors (Var, Lam, App, Pi, Rcd, Match, Ctr, Hole, Lit, Ann, Call, Comptime, Dot)
- `Value` types - Normalization by evaluation
- Type checker - Bidirectional type checking (infer/check)
- Unifier - Type unification with occurs check
- FFI/Comptime - Compile-time evaluation with permissions
- Exhaustiveness checking - Maranget's algorithm
- **263 tests passing** for core module

**Tao AST** (`src/tao/ast.gleam`):
- Complete AST definition (~430 lines)
- Desugaring to core (~550 lines)
- **Compiles successfully**

### ⏳ In Progress

**Core Language Changes for Tao Integration**:

| Change | Priority | Effort | Status |
|--------|----------|--------|--------|
| Untyped literals | HIGH | ~100 lines | 📋 Planned |
| Pattern guards | MEDIUM | ~50 lines | 📋 Planned |
| Coercion term | HIGH | ~30 lines | 📋 Planned |
| Overload metadata | LOW | ~30 lines | 📋 Planned |

See **[04-tao-integration.md](./04-tao-integration.md)** for detailed integration plan.

**Core Syntax** (`src/core/syntax.gleam`):
- ✅ Minimal skeleton with 4 Term variants
- ✅ Variables: `x` → `Var(0)`
- ✅ Literals: `42` → `Lit(I32(42))`
- ✅ Lambda: `λx. x` → `Lam("x", body)`
- ✅ Application: `f(x)` → `App(fun, arg)`
- ✅ Precedence-based parenthesization
- ✅ Round-trip tests (parse → format → parse)
- **18 tests passing** for core syntax

### 📋 Pending

**Core Syntax Expansion** - Adding remaining Term variants:

| Phase | Terms | Status |
|-------|-------|--------|
| Phase 1 | Var, Lit, Lam, App | ✅ Complete |
| Phase 2 | Hole, Typ, LitT | 📋 Planned |
| Phase 3 | Ann, Dot, Ctr | 📋 Planned |
| Phase 4 | Pi, Rcd | 📋 Planned |
| Phase 5 | Match, Call, Comptime | 📋 Planned |
| Phase 6 | Source location tracking | 📋 Planned |

**Tao Integration**:
- [ ] Add untyped literals to `Literal` type
- [ ] Add `Coerce` term for type coercion
- [ ] Add pattern guards to `Case` type
- [ ] Update exhaustiveness checking for guards
- [ ] Add overload metadata to `State`
- [ ] Integration tests (Tao → Core → Evaluate)

**Source location tracking** - Proper `Span` with filename, start/end line/column (see **[../grammar/05-source-location-tracking.md](../grammar/05-source-location-tracking.md)**)
**De Bruijn conversion** - Proper name ↔ index conversion (currently all vars become `Var(0)`)
**Full Term coverage** - All 13 Term variants with complete parsing/formatting
**Pattern grammar** - Full pattern matching syntax
**Integration** - Wire up `core/syntax` with `core/core` evaluator and type checker

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL with parser/formatter generation
│   ├── lexer.gleam        # Tokenizer
│   └── formatter.gleam    # Document algebra
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker, FFI
│   ├── syntax.gleam       # Core language grammar (single source of truth) ← NEW
│   └── ...                # Other core modules
├── examples/
│   └── calc.gleam         # Working calculator example
└── ...

test/
├── core/
│   ├── core_test.gleam    # Core module tests (263 passing)
│   └── syntax_test.gleam  # Core syntax tests (18 passing) ← NEW
└── ...

docs/
├── syntax-library.md      # Syntax library user documentation ← NEW
└── plans/
    ├── grammar/           # Grammar system plans
    └── core/              # Core language plans
        ├── 01-overview.md # This file
        ├── 02-syntax.md   # Syntax specification
        └── 03-ffi-comptime.md # FFI/comptime docs
```

---

## Key Concepts

### Grammar-Generated Parser and Formatter

```gleam
// Single grammar definition
pub fn core_grammar() -> grammar.Grammar(Term) {
  use g <- grammar.define
  g
  |> grammar.rule("Lambda", [
    grammar.alt(
      grammar.seq([/* pattern */]),
      make_lambda,      // constructor: values → AST
      format_term,      // formatter: AST → Doc
    ),
  ])
}

// Both parser and formatter derived from grammar
pub fn parse(source: String) -> grammar.ParseResult(Term) {
  grammar.parse(core_grammar(), source)
}

pub fn format(term: Term) -> String {
  grammar.format(core_grammar(), term)
}
```

### Precedence-Based Parenthesization

```gleam
fn format_term(term, parent_prec) {
  case term.data {
    Lam(name, body) -> {
      let inner = formatter.concat([/* ... */])
      wrap_parens(inner, 70 < parent_prec)  // Add parens if needed
    }
    App(fun, arg) -> {
      let inner = formatter.concat([/* ... */])
      wrap_parens(inner, 85 < parent_prec)
    }
  }
}
```

Example:
- `format(App(Lam("x", Var(0)), Lit(I32(42))))` → `"(λx. var0)(42)"`
- `format(Lam("x", App(Var(0), Lit(I32(42)))))` → `"λx. var0(42)"`

---

## Example Usage

```gleam
import core/syntax

// Parse source code
let source = "λx. f(x)"
let result = syntax.parse(source)
// result.ast = Term(Lam("x", App(Var(0), Var(0))), _)

// Format AST back to source
let formatted = syntax.format(result.ast)
// formatted = "λx. var0(var0)"

// Note: Identifiers become var0 (De Bruijn index)
// Full implementation will preserve names with proper conversion
```

---

## Related Documents

- **[02-syntax.md](./02-syntax.md)** - Detailed syntax specification with grammar rules
- **[03-ffi-comptime.md](./03-ffi-comptime.md)** - FFI and comptime implementation (✅ complete)
- **[../grammar/01-overview.md](../grammar/01-overview.md)** - Grammar system overview
- **[../../syntax-library.md](../../syntax-library.md)** - Syntax library user docs

---

## References

- [Syntax Library](../../src/syntax/grammar.gleam)
- [Core Syntax](../../src/core/syntax.gleam)
- [Core Language](../../src/core/core.gleam)
- [Calculator Example](../../src/examples/calc.gleam)
- [Syntax Tests](../../test/core/syntax_test.gleam)
