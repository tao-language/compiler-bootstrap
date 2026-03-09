# Core Language Overview

> **Status**: ✅ **Complete** - All 13 Term variants with proper variable shadowing (401 tests passing)
> **Date**: March 2025 (Updated)

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
│  src/core/syntax.gleam (single source of truth, ~1150 lines)    │
│  ├── NamedTerm          - Intermediate AST with named variables │
│  ├── NamedPattern       - Pattern AST with named variables      │
│  ├── NamedCase          - Match case AST                        │
│  ├── ParseValue         - Multi-type grammar wrapper            │
│  ├── core_grammar()     - Complete grammar definition           │
│  ├── parse()            - Two-pass parser                       │
│  └── format()           - Full formatter with pattern support   │
│                                                                  │
│  Grammar → Parser + Formatter                                    │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │  grammar.alt(pattern, constructor, formatter)            │   │
│  │  - pattern: what to match                                │   │
│  │  - constructor: values → NamedTerm                       │   │
│  │  - formatter: NamedTerm → Doc                            │   │
│  └──────────────────────────────────────────────────────────┘   │
│                                                                  │
│  NamedTerm → Term (De Bruijn conversion with env tracking)      │
│  ┌──────────────────────────────────────────────────────────┐   │
│  │  named_to_de_bruijn_loop(term, env)                      │   │
│  │  - NVar("x") → Var(0) if "x" is innermost in env         │   │
│  │  - NLam("x", body) → Lam("x", body_db) with [x, ..env]   │   │
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
6. **Two-pass parsing** - NamedTerm → Term conversion with proper variable shadowing

---

## Implementation Status

### ✅ Complete and Working

**Syntax Library** (`src/syntax/`):
- ✅ Lexer - Tokenizes identifiers, keywords, numbers, strings, comments, operators
- ✅ Grammar DSL - Full layout-aware grammar definition with `Alternative` type
- ✅ Formatter - Document algebra with best-fit rendering
- ✅ Calculator example - Working parser/formatter with +, -, *, /
- ✅ Multi-character operators (`->`, `==`, `!=`, `<-`)
- ✅ Constructor keywords removed (now `#True`, `#Some`, etc.)
- ✅ Type/literal type prefixes (`$Type`, `$I32`)
- ✅ **All syntax library tests passing**

**Core Syntax** (`src/core/syntax.gleam`):
- ✅ **All 13 Term variants** with complete parsing and formatting
- ✅ **Two-pass parsing** with `NamedTerm` intermediate AST
- ✅ **Variable shadowing** - `x -> y -> x` correctly preserves outer `x`
- ✅ **Pattern matching** - Wildcards, as-patterns, constructor patterns
- ✅ **Records with fields** - `{}`, `{x: 1}`, `{x: 1, y: 2, z: 3}`
- ✅ **ASCII syntax** - `x -> y` (not `λx. y`), `(x : A) -> B` (not `→`)
- ✅ **Constructor prefix** - `#True`, `#Some(x)` (not bare `True`)
- ✅ **Type prefix** - `$Type`, `$Type(1)`, `$I32`, `$F64`
- ✅ **Hole IDs** - `?`, `?1`, `?2`
- ✅ **Full formatter** - All terms format correctly with precedence
- ✅ **Source locations** - Full span tracking from tokens
- ✅ **401 tests passing**

**Core Language** (`src/core/core.gleam`):
- ✅ `Term` types - All 13 constructors
- ✅ `Value` types - Normalization by evaluation
- ✅ Type checker - Bidirectional type checking (infer/check)
- ✅ Unifier - Type unification with occurs check
- ✅ FFI/Comptime - Compile-time evaluation with permissions
- ✅ Exhaustiveness checking - Maranget's algorithm
- ✅ **263 tests passing** for core module

### 📋 Future Work

**Tao Integration** (if needed):
- [ ] Add untyped literals to `Literal` type
- [ ] Add `Coerce` term for type coercion
- [ ] Add pattern guards to `Case` type
- [ ] Integration tests (Tao → Core → Evaluate)

See **[04-tao-integration.md](./04-tao-integration.md)** for detailed integration plan.

**Potential Enhancements**:
- [ ] Trailing commas in records and argument lists
- [ ] Label shorthand in records (`{x}` instead of `{x: x}`)
- [ ] Multi-line formatting for long records/cases
- [ ] Better error messages with source locations

---

## Complete Term Coverage

| Term | Syntax | Status |
|------|--------|--------|
| `Var` | `x` | ✅ Complete |
| `Lit` | `42` | ✅ Complete |
| `Lam` | `x -> body` | ✅ Complete |
| `App` | `f(x)` | ✅ Complete |
| `Pi` | `(x : A) -> B` | ✅ Complete |
| `Ann` | `x : $I32` | ✅ Complete |
| `Dot` | `record.field` | ✅ Complete |
| `Ctr` | `#True`, `#Some(x)` | ✅ Complete |
| `Rcd` | `{}`, `{x: 1, y: 2}` | ✅ Complete |
| `Hole` | `?`, `?1` | ✅ Complete |
| `Typ` | `$Type`, `$Type(1)` | ✅ Complete |
| `LitT` | `$I32`, `$F64` | ✅ Complete |
| `Match` | `match x with ... returning ...` | ✅ Complete |
| `Call` | `call name(args)` | ✅ Complete |
| `Comptime` | `comptime { term }` | ✅ Complete |

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL with parser/formatter generation
│   ├── lexer.gleam        # Tokenizer with full position tracking
│   └── formatter.gleam    # Document algebra with best-fit rendering
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker, FFI
│   └── syntax.gleam       # Core language grammar (~1150 lines) ✅ COMPLETE
│       ├── NamedTerm      # Intermediate AST (12 variants)
│       ├── NamedPattern   # Pattern AST (7 variants)
│       ├── NamedCase      # Match case AST
│       ├── ParseValue     # Multi-type wrapper (5 variants)
│       ├── core_grammar() # Complete grammar definition
│       ├── parse()        # Two-pass parser
│       ├── format()       # Full formatter
│       └── 50+ helpers    # Constructors, formatters, converters
├── examples/
│   └── calc.gleam         # Working calculator example
└── ...

test/
├── core/
│   ├── core_test.gleam    # Core module tests (263 passing)
│   └── syntax_test.gleam  # Core syntax tests (40+ passing)
└── ...

docs/
├── syntax-library.md      # Syntax library user documentation
└── plans/
    ├── grammar/           # Grammar system plans
    │   ├── 01-overview.md
    │   ├── 02-grammar-dsl.md
    │   ├── 03-formatter.md
    │   ├── 04-layout.md
    │   ├── 05-source-location-tracking.md ✅ COMPLETE
    │   └── 06-records-with-fields.md ✅ COMPLETE
    └── core/              # Core language plans
        ├── 01-overview.md # This file
        ├── 02-syntax.md   # Syntax specification ✅ UPDATED
        ├── 03-variable-shadowing.md ✅ COMPLETE
        ├── 03-ffi-comptime.md # FFI/comptime docs
        └── 04-tao-integration.md # Tao integration plan
```

---

## Key Concepts

### Two-Pass Parsing (Variable Shadowing)

```gleam
// Pass 1: Grammar builds NamedTerm with string names
pub type NamedTerm {
  NVar(name: String, span: Span)
  NLam(name: String, body: NamedTerm, span: Span)
  NPi(name: String, in: NamedTerm, out: NamedTerm, span: Span)
  // ... 12 variants
}

// Pass 2: Convert to Term with De Bruijn indices
fn named_to_de_bruijn_loop(term: NamedTerm, env: List(String)) -> Term {
  case term {
    NVar(name, span) -> {
      case find_in_env(env, name, 0) {
        Ok(index) -> Term(Var(index), span)  // Found binding
        Error(_) -> Term(Var(0), span)       // Free variable
      }
    }
    NLam(name, body, span) -> {
      let body_db = named_to_de_bruijn_loop(body, [name, ..env])
      Term(Lam(name, body_db), span)
    }
    // ... other cases
  }
}

// Public API composes both passes
pub fn parse(source: String) -> ParseResult(Term) {
  let parsed = grammar.parse(core_grammar(), source)
  case parsed {
    Ok(AsTerm(named_term)) -> Ok(named_to_de_bruijn(named_term))
    // ...
  }
}
```

**Result**: `x -> y -> x` correctly preserves outer `x` reference (index 1).

### Multi-Type Grammar

```gleam
pub type ParseValue {
  AsTerm(NamedTerm)
  AsFields(List(#(String, NamedTerm)))
  AsCases(List(NamedCase))
  AsPattern(NamedPattern)
  AsArgs(List(NamedTerm))
}
```

Allows grammar rules to return different types (terms, field lists, cases, patterns, args).

### Precedence-Based Parenthesization

```gleam
fn format_term(term, parent_prec, bindings) {
  case term.data {
    Lam(name, body) -> {
      let inner = formatter.concat([
        formatter.text(name),
        formatter.text(" -> "),
        format_term(body, 70, [name, ..bindings]),
      ])
      wrap_parens(inner, 70 < parent_prec)
    }
    App(fun, arg) -> {
      let inner = formatter.concat([
        format_term(fun, 85, bindings),
        formatter.text("("),
        format_term(arg, 85, bindings),
        formatter.text(")"),
      ])
      wrap_parens(inner, 85 < parent_prec)
    }
  }
}
```

Example:
- `format(App(Lam("x", Var(0)), Lit(I32(42))))` → `"(x -> var0)(42)"`
- `format(Lam("x", App(Var(0), Lit(I32(42)))))` → `"x -> var0(42)"`

---

## Example Usage

```gleam
import core/syntax

// Parse source code
let source = "x -> y -> x"
let result = syntax.parse(source)
// result.ast = Term(Lam("x", Lam("y", Var(1))), _)
// Note: Var(1) correctly refers to outer x!

// Format AST back to source
let formatted = syntax.format(result.ast)
// formatted = "x -> y -> x"  // Correct!

// Pattern matching
let match_source = "match opt with $Type returning _ -> #None, #Some(x) -> x"
let match_result = syntax.parse(match_source)
// Correctly parses patterns and bodies

// Records
let record_source = "{x: 1, y: 2, z: 3}"
let record_result = syntax.parse(record_source)
// Correctly parses multiple fields
```

---

## Test Coverage

**401 tests passing** covering:
- ✅ Round-trip tests for all 13 term types
- ✅ Variable shadowing scenarios (`x -> y -> x`, `x -> x -> x`)
- ✅ Pattern matching syntax (wildcards, as-patterns, constructors)
- ✅ Records with 0, 1, and multiple fields
- ✅ Constructor syntax with and without arguments
- ✅ Type universes and literal types
- ✅ Holes with and without IDs
- ✅ Precedence and parenthesization
- ✅ Lexer token recognition
- ✅ Formatter output verification

---

## Related Documents

- **[02-syntax.md](./02-syntax.md)** - Detailed syntax specification with grammar rules ✅ UPDATED
- **[03-variable-shadowing.md](./03-variable-shadowing.md)** - Variable shadowing implementation plan ✅ COMPLETE
- **[03-ffi-comptime.md](./03-ffi-comptime.md)** - FFI and comptime implementation ✅ COMPLETE
- **[04-tao-integration.md](./04-tao-integration.md)** - Tao integration plan
- **[../grammar/05-source-location-tracking.md](../grammar/05-source-location-tracking.md)** - Source location tracking ✅ COMPLETE
- **[../grammar/06-records-with-fields.md](../grammar/06-records-with-fields.md)** - Records with fields plan ✅ COMPLETE
- **[../../syntax-library.md](../../syntax-library.md)** - Syntax library user docs

---

## References

- [Syntax Library](../../src/syntax/grammar.gleam)
- [Core Syntax](../../src/core/syntax.gleam)
- [Core Language](../../src/core/core.gleam)
- [Calculator Example](../../src/examples/calc.gleam)
- [Syntax Tests](../../test/core/syntax_test.gleam)
