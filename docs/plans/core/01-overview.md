# Core Language Overview

> **Status**: Grammar system complete, core language grammar pending
> **Date**: March 2025

---

## Core Principle

**The grammar is the single source of truth.** It defines:
1. What to parse (patterns)
2. How to construct AST from parsed values (constructors)
3. How to deconstruct AST back to values (deconstructors)
4. How to format values back to source (layout hints)

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

## Syntax Overview

### Atoms

```typescript
// Variables
x
foo
myVar

// Literals
42
3.14
"hello"

// Holes (metavariables)
?
?0

// Parenthesized expressions
(x)
((x))
```

### Application (C-style only)

```typescript
// Single argument
f(x)

// Multiple arguments (curried)
f(x, y)
// Desugars to: (f(x))(y)

// Nested application
f(g(x))
f(g(x), h(y))
```

### Lambda Abstraction

```typescript
// Single parameter
λx. x

// Multiple parameters (sugar for nested lambdas)
λx y z. x + y + z
// Desugars to: λx. λy. λz. x + y + z

// With type annotation
λ(x: Type). x
```

### Pi Types (Dependent Function Types)

```typescript
// Basic Pi type
(x: A) → B

// When x not used in B (regular function type)
(_: A) → B
A → B  // Sugar for (_: A) → B

// Multiple parameters (sugar for nested Pi)
(x: A, y: B) → C
// Desugars to: (x: A) → (y: B) → C
```

### Records

```typescript
// Record type
{x: Int, y: Int}

// Record value
{x: 1, y: 2}

// Empty record
{}

// Field access
r.x
r.field

// Nested access
r.x.y
```

### Constructors

```typescript
// Nullary constructor
Nil
True
False

// Unary constructor
Cons(1)
Some(42)

// Multiple arguments (curried application)
Cons(1, Nil)
// Desugars to: (Cons(1))(Nil)
```

### Match Expressions

```typescript
// Basic match
match x {
  A → 1,
  B → 2
}

// With patterns
match list {
  Nil → 0,
  Cons(head, tail) → 1 + length(tail)
}

// With guards
match x {
  n if n > 0 → "positive",
  _ → "negative"
}
```

### Type Annotations

```typescript
// Term annotation
x: Type
(λx. x): (A → B)
f(x): ReturnType
```

### Comptime

```typescript
// Compile-time evaluation
comptime add(1, 2)
// Evaluates to: 3

// Non-concrete args deferred to runtime
comptime add(get_input(), 1)
// Deferred: add(get_input(), 1)
```

---

## Precedence and Associativity

### Precedence Table (highest to lowest)

| Prec | Operator/Syntax | Assoc | Example |
|------|-----------------|-------|---------|
| 100 | Atom | - | `x`, `42`, `λx. x` |
| 95 | Field access | Left | `r.x.y` |
| 90 | Constructor app | Left | `Cons(1, Nil)` |
| 85 | C-style app | Left | `f(x, y)` |
| 75 | Type annotation | Right | `x: A: B` |
| 70 | Lambda | Right | `λx. λy. x` |
| 65 | Pi type | Right | `(x: A) → (y: B) → C` |
| 60 | Match | - | `match x { ... }` |

### Examples

```typescript
// Application
f(x)(y)      // = (f(x))(y)
f(g(x))      // = f(g(x))
f(x, y)(z)   // = (f(x, y))(z)

// Lambda vs application
λx. f(x)     // = λx. (f(x))
(λx. f)(x)   // = ((λx. f)(x))

// Type annotation
f(x): T      // = (f(x)): T
f(x: T)      // = f((x: T))
```

---

## Implementation Status

### ✅ Complete and Working

1. **Lexer** - Tokenizes all core language tokens:
   - Identifiers and keywords (λ, Type, I32, etc.)
   - Numbers (integers and floats)
   - Strings with escape sequences
   - Operators and punctuation
   - Comments (line and block)

2. **Grammar DSL** - Full layout-aware grammar definition:
   - `FormatterConfig` - Global settings (width, indent)
   - `LayoutHint` - Per-item hints (SoftBreak, HardBreak, Space, NoSeparator)
   - `OperatorLayout` - Operator formatting (separator, break positions, indent)
   - `SeqWithLayout` - Sequences with layout hints between elements
   - All pattern types (Token, Keyword, Ref, Seq, Choice, Opt, Many, Sep1, Parens)

3. **Parser** - Handles all grammar constructs:
   - `parse_pattern()` - Dispatches on pattern type
   - `parse_seq_with_layout()` - Parses sequences with hints
   - `parse_left_assoc()` - Left-associative operator parsing
   - Error handling and position tracking

4. **Formatter** - Layout-aware formatting:
   - `format_binary_op()` - Formats binary operators with layout
   - `format_sequence_with_layout()` - Formats sequences with hints
   - Precedence-based parenthesization
   - Soft/hard line breaks

5. **Tests** - 238 tests passing:
   - Parser tests
   - Formatter tests
   - Round-trip tests (parse → format → parse)

6. **FFI/Comptime** - Compile-time evaluation:
   - Pure built-in functions (arithmetic, comparison, logical)
   - Permission system (AllowRead, AllowWrite)
   - Lazy evaluation (non-concrete args deferred to runtime)
   - 263 tests passing

### ⏳ Pending

1. **Core Language Grammar Definition** - Need to create `src/core/grammar.gleam`
2. **Constructor/Deconstructor Functions** - Map parsed values to `Term` constructors
3. **Core Formatter** - Implement `format_term()` for all `Term` variants
4. **De Bruijn Conversion** - Handle name ↔ index conversion
5. **Integration** - Wire up parser/formatter with existing core module

---

## File Structure

```
src/
├── syntax/
│   ├── grammar.gleam      # Grammar DSL + parser + formatter generators
│   ├── formatter.gleam    # Document algebra (unchanged)
│   └── lexer.gleam        # Tokenizer (unchanged)
├── core/
│   ├── core.gleam         # Term types, evaluator, type checker (unchanged)
│   ├── grammar.gleam      # Core language grammar definition ← MAIN WORK
│   ├── parser.gleam       # Thin wrapper: grammar.parse(core_grammar(), src)
│   └── formatter.gleam    # Thin wrapper: grammar.format(core_grammar(), ast)
└── ...
```

---

## Related Documents

- **[02-syntax.md](./02-syntax.md)** - Detailed syntax specification with grammar rules
- **[03-ffi-comptime.md](./03-ffi-comptime.md)** - FFI and comptime implementation
- **[04-implementation-plan.md](./04-implementation-plan.md)** - Implementation roadmap

---

## References

- [Grammar System Plans](../grammar/01-overview.md)
- [Core Language Specification](../core.md)
