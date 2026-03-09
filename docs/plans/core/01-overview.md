# Core Language Overview

> **Status**: ✅ FFI/Comptime complete, ⏳ Core language grammar pending
> **Date**: March 2025

---

## Core Principle

**The grammar is the single source of truth.** It defines:
1. What to parse (patterns)
2. How to construct AST from parsed values (constructors)
3. How to format values back to source (formatters)
4. How to handle compile-time evaluation (comptime)

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     Compiler Pipeline                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Source → Parse → Elaborate (infer/check) → Codegen            │
│                │    │                          │                 │
│                │    └─ Returns #(Value, Type, State)            │
│                │       - Comptime blocks resolved here          │
│                │       - Unknown FFI → VCall (runtime defer)    │
│                └─ Raw AST with Call/Comptime nodes               │
│                                                                  │
│  Codegen → Backend Module (user or official)                     │
│            └─ Maps VCall to target runtime calls                 │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Design Principles

1. **TypeScript-like syntax** - Familiar to web developers
2. **C-style application only** - `f(x, y)` not `f x y`
3. **Simple grammar** - No ambiguity between constructs
4. **Clear precedence** - Obvious grouping without excessive parentheses
5. **Minimal boilerplate** - No unnecessary keywords

---

## Implementation Status

### ✅ Complete and Working

**Syntax Library** (`src/syntax/`):
- Lexer (~400 lines) - Tokenizes identifiers, keywords, numbers, strings, comments
- Grammar DSL (~786 lines) - Full layout-aware grammar definition
- Formatter (~139 lines) - Document algebra with best-fit rendering
- Calculator example - Working parser/formatter with +, -, *, /

**Core Language** (`src/core/`):
- `Term` types - Var, Lam, App, Pi, Rcd, Match, Ctr, Hole, Lit, Ann, Call, Comptime
- `Value` types - Normalization by evaluation
- Type checker - Bidirectional type checking (infer/check)
- Unifier - Type unification with occurs check
- FFI/Comptime - Compile-time evaluation with permissions
  - Pure builtins (add, sub, mul, div, eq, lt, etc.)
  - Permission system (AllowRead, AllowWrite)
  - `VCall` for deferred runtime calls
  - **263 tests passing**

### ⏳ Pending

- **Core language grammar** - Need to create `src/core/grammar.gleam`
- **Core language parser** - Thin wrapper around syntax library parser
- **Core language formatter** - Manual formatter using syntax formatter
- **De Bruijn conversion** - Handle name ↔ index conversion
- **Integration** - Wire up syntax library with core language

---

## Syntax Library Status

The syntax library (`src/syntax/`) is **complete and working**:

- ✅ Lexer with comment handling, position tracking
- ✅ Grammar DSL with layout hints
- ✅ Parser with operator precedence
- ✅ Formatter with document algebra
- ✅ Calculator example demonstrates full round-trip

See **[../grammar/01-overview.md](../grammar/01-overview.md)** for details.

---

## FFI/Comptime Status

The FFI/comptime system is **complete and working**:

- ✅ `Call` and `Comptime` term constructors
- ✅ `VCall` value for deferred runtime calls
- ✅ Pure builtins (arithmetic, comparison, logical)
- ✅ Permission system (AllowRead, AllowWrite)
- ✅ Write fulfills Read (not vice versa)
- ✅ **263 tests passing**

See **[03-ffi-comptime.md](./03-ffi-comptime.md)** for details.

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL (~786 lines)
│   ├── lexer.gleam        # Tokenizer (~400 lines)
│   └── formatter.gleam    # Document algebra (~139 lines)
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker, FFI
│   ├── grammar.gleam      # Core language grammar definition ← TODO
│   ├── parser.gleam       # Thin wrapper: syntax.parse(core_grammar(), src) ← TODO
│   └── formatter.gleam    # Manual formatter using syntax formatter ← TODO
└── examples/
    └── calc.gleam         # Working calculator example
```

---

## Related Documents

- **[02-syntax.md](./02-syntax.md)** - Detailed syntax specification with grammar rules
- **[03-ffi-comptime.md](./03-ffi-comptime.md)** - FFI and comptime implementation
- **[../grammar/01-overview.md](../grammar/01-overview.md)** - Grammar system overview
- **[../../syntax-library.md](../../syntax-library.md)** - Syntax library user docs

---

## References

- [Syntax Library](../../src/syntax/grammar.gleam)
- [Core Language](../../src/core/core.gleam)
- [Calculator Example](../../src/examples/calc.gleam)
