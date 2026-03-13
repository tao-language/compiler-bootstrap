# Tao Language Overview

> **Goal**: Simple, pragmatic functional language with dependent types—TypeScript-like syntax without the complexity
> **Status**: ⏳ **MVP Implementation In Progress** - Starting Week 1 (Lexer + Parser)
> **Date**: March 2025 (Updated: March 2026 - MVP started)

---

## Core Insight

**99% of code should look like simple TypeScript. 1% should have access to full dependent types when needed.**

Tao is syntax sugar over the core language. All heavy lifting (type checking, normalization, evaluation) is done by `src/core/core.gleam`. Tao adds:
- Familiar syntax (TypeScript-like)
- Operator overloading via type inference
- Result/Maybe sugar (`<-`, `?.`, `?`)
- Explicit mutability (`let mut`)
- No OOP, no async/await, no null

---

## Current Status

### ✅ Complete

**Tao AST** (`src/tao/ast.gleam`):
- ✅ All type definitions (Program, Declaration, Expr, Pattern, Type, etc.)
- ✅ Span tracking for all nodes
- ✅ Compiles successfully
- ⚠️ **No tests yet** - will add during MVP implementation

### ⏳ In Progress

**Tao MVP Implementation** (2-3 weeks, started March 2026):

| Component | Status | Week |
|-----------|--------|------|
| **Tao Lexer** | 📋 Planned | Week 1 |
| **Tao Grammar** | 📋 Planned | Week 1 |
| **Tao Desugarer** | 📋 Planned | Week 2 |
| **CLI Integration** | 📋 Planned | Week 3 |
| **Examples + Tests** | 📋 Planned | Week 3 |

See **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** for detailed MVP implementation plan.

### 📋 Next Steps (After MVP)

1. **Phase 1**: Tao MVP (lexer, grammar, desugarer) - 2-3 weeks ⏳ IN PROGRESS
2. **Phase 2**: Core standard library - 1 week
3. **Phase 3**: Tao expansion (do blocks, mut, imports) - 2-3 weeks
4. **Phase 4**: Tao standard library - 2-3 weeks
5. **Phase 5**: Polish (error suggestions, docs) - Ongoing

---

## Architecture

### Module Structure

```
src/
├── tao/
│   ├── ast.gleam              # ✅ Tao AST (~430 lines)
│   ├── lexer.gleam            # ⏳ TODO (~300 lines)
│   ├── grammar.gleam          # ⏳ TODO (~400 lines)
│   └── desugar.gleam          # ⏳ TODO (~300 lines)
├── syntax/                    # ✅ Reuse existing syntax library
│   ├── grammar.gleam          # ✅ Grammar DSL (~1100 lines)
│   ├── lexer.gleam            # ✅ Tokenizer (~400 lines)
│   ├── formatter.gleam        # ✅ Document algebra (~440 lines)
│   ├── source_snippet.gleam   # ✅ Source snippet (~260 lines)
│   └── error_reporter.gleam   # ✅ Error reporting (~220 lines)
└── core/                      # ✅ Reuse existing core language
    ├── syntax.gleam           # ✅ Core syntax (~1677 lines)
    └── core.gleam             # ✅ Type checker, evaluator (~1942 lines)
```

### Compilation Pipeline

```
Tao Source (.tao)
    ↓
Tao Lexer (src/tao/lexer.gleam)
    ↓
Tao Parser (src/tao/grammar.gleam + syntax library)
    ↓
Tao AST
    ↓
Tao Desugar (src/tao/desugar.gleam)
    ↓
Core Term
    ↓
Core Type Checker + Evaluator
    ↓
Result
```

### Data Flow

```
┌─────────────────────────────────────────────────────────────────┐
│  Tao Source (.tao)                                              │
│  fn add(x: Int, y: Int): Int { x + y }                          │
└─────────────────────────────────────────────────────────────────┘
                            ↓ (tokenize)
┌─────────────────────────────────────────────────────────────────┐
│  Tokens                                                         │
│  [Fn, Ident("add"), LParen, Ident("x"), Colon, Int, ...]       │
└─────────────────────────────────────────────────────────────────┘
                            ↓ (parse)
┌─────────────────────────────────────────────────────────────────┐
│  Tao AST                                                        │
│  FnDecl("add", [Param("x", Int), Param("y", Int)], ...)        │
└─────────────────────────────────────────────────────────────────┘
                            ↓ (desugar)
┌─────────────────────────────────────────────────────────────────┐
│  Core Term                                                      │
│  Lam("x", Lam("y", Call("i32_add", Var(1), Var(0))))           │
└─────────────────────────────────────────────────────────────────┘
                            ↓ (type check + eval)
┌─────────────────────────────────────────────────────────────────┐
│  Result                                                         │
│  VLam("x", ..., Lam("y", ..., Call(...)))                       │
└─────────────────────────────────────────────────────────────────┘
```

---

## Design Principles

### 1. TypeScript-like Syntax

Familiar to web developers:
```tao
fn add(x: Int, y: Int): Int {
  x + y
}

let result = add(5, 10)
```

### 2. Sensible Defaults

99% of code is simple, 1% uses dependent types:
```tao
// Simple case (99%)
let x = 5

// Dependent type case (1%)
let v: Vec(5, Int) = [1, 2, 3, 4, 5]
```

### 3. Core as Foundation

Tao desugars to Core, which handles:
- Type checking
- Normalization
- Evaluation
- Exhaustiveness checking

### 4. Error Messages First

Error messages designed alongside implementation:
- Clear, actionable hints
- Source snippets with context
- Emoji-guided navigation

---

## MVP Features

### In Scope ✅

| Feature | Syntax | Desugars To |
|---------|--------|-------------|
| **Functions** | `fn f(x: Int): Int { x }` | Core `Lam` |
| **Let bindings** | `let x = 5` | Core `Let` |
| **Pattern match** | `match x { \| Some(y) -> y }` | Core `%match` |
| **Operators** | `x + y` | Core `%call i32_add` |
| **If expressions** | `if c { a } else { b }` | Core `Match` |
| **Basic types** | `Int`, `Bool`, `String` | Core types |

### Out of Scope ❌ (For Now)

| Feature | Why Deferred |
|---------|--------------|
| Mutable variables | Complexity, use Core directly |
| Do blocks | Desugaring complexity |
| Imports/modules | Single-file programs first |
| Generics | Core handles polymorphism |
| Advanced types | Use Core for dependent types |

---

## Example Programs

### Hello World

```tao
// examples/tao/01_hello.tao
fn main() {
  print("Hello, Tao!")
}
```

### Factorial

```tao
// examples/tao/02_factorial.tao
fn factorial(n: Int): Int {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}

fn main() {
  factorial(5)
}
```

### Option Type

```tao
// examples/tao/03_option.tao
type Option<a> = Some(a) | None

fn unwrap(opt: Option<Int>): Int {
  match opt {
    | Some(x) -> x
    | None -> 0
  }
}
```

---

## Related Documents

- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - MVP implementation plan ⏳ **START HERE**
- **[06-implementation-plan.md](./06-implementation-plan.md)** - Full implementation plan
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[07-desugaring-specification.md](./07-desugaring-specification.md)** - Detailed desugaring
- **[../../docs/core-syntax.md](../../docs/core-syntax.md)** - Core syntax reference
- **[../../docs/cli.md](../../docs/cli.md)** - CLI documentation

---

## References

- [Tao AST](../../src/tao/ast.gleam) - Already complete ✅
- [Syntax Library](../../src/syntax/grammar.gleam) - Reuse for parsing
- [Core Language](../../src/core/core.gleam) - Compilation target
- [CLI](../../src/compiler_bootstrap.gleam) - Integration point

---

**Ready to implement Tao MVP! 🚀**
