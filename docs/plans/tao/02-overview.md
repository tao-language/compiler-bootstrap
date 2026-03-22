# Tao Language Overview

> **Goal**: Simple, pragmatic functional language with dependent types—TypeScript-like syntax without the complexity
> **Status**: ✅ **Complete** - Core language, Stmt system, imports, and test framework fully functional (519 tests passing)
> **Date**: March 2026 (Updated: March 2026 - Post reorganization)

---

## Core Insight

**99% of code should look like simple TypeScript. 1% should have access to full dependent types when needed.**

Tao is syntax sugar over the core language. All heavy lifting (type checking, normalization, evaluation) is done by `src/core/core.gleam`. Tao adds:
- Familiar syntax (TypeScript-like)
- Operator overloading via type inference
- Result/Maybe sugar (`<-`, `?.`, `?`)
- Explicit mutability (`let mut`)
- **Modules as Records** - every module returns a Record of public names
- **Imports as Let Aliases** - all imports desugar to `let` bindings
- No OOP, no async/await, no null

---

## Current Status

### ✅ Complete

**Tao Core** - Expression parsing, overloading, type matching, pattern matching, and CLI integration:

| Component | Status | Description |
|-----------|--------|-------------|
| **Tao Lexer** | ✅ Complete | Tokenizes identifiers, numbers, operators, keywords, `@`, `..` |
| **Tao Grammar** | ✅ Complete | Parses expressions, overloaded functions, match with patterns |
| **Tao Formatter** | ✅ Complete | Formats expressions, overloaded functions, patterns |
| **Tao Desugarer** | ✅ Complete | Transforms Tao → Core with type matching and pattern conversion |
| **Type Matching** | ✅ Complete | Generates match expressions on type parameters |
| **Pattern Matching** | ✅ 80% Complete | Wildcard, variable, literal, constructor patterns work; tuple/record/list/or/as need grammar fixes |
| **CLI Integration** | ✅ Complete | `gleam run run file.tao` works |
| **Examples** | ✅ Complete | Pattern matching examples working |
| **Tests** | ✅ 519 passing | All tests green |

**Core Features**:
- ✅ Numbers: `42`, `3.14`
- ✅ Variables: `x`, `myVar`
- ✅ Arithmetic: `+`, `-`, `*`, `/`
- ✅ Correct precedence: `*` binds tighter than `+`
- ✅ Left associativity: `10 - 5 - 2 = (10 - 5) - 2`
- ✅ Parentheses: `(1 + 2) * 3`
- ✅ **Overloading**: `fn (+)(x: I32) -> I32 { x + 1 }`
- ✅ **Type Matching**: Implicit type params with match expressions
- ✅ **Pattern Matching**: `match x { | Some(n) -> n | None -> 0 }`
- ✅ **Match Guards**: `match x { | n if n > 0 -> 1 | _ -> 0 }`
- ✅ Desugaring: `x + y` → `%call i32_add(x, y)`
- ✅ Type checking via Core
- ✅ Evaluation via Core

**Pattern Matching Status**:
- ✅ Wildcard: `_`
- ✅ Variable: `n`
- ✅ Literal: `0`, `1`
- ✅ Constructor: `Some(x)`, `None`, `True`, `False`
- ✅ Guards: `n if n > 0`
- ⏳ Tuple: `(a, b)` - AST ready, grammar pending
- ⏳ Record: `{x, y}` - AST ready, grammar pending
- ⏳ List: `[h, ..t]` - AST ready, grammar pending
- ⏳ Or: `p1 | p2` - AST ready, grammar pending
- ⏳ As: `x @ pattern` - AST ready, grammar pending

**Example Usage**:
```bash
# Run a Tao program
gleam run run examples/tao/01_arithmetic.tao
# Output: %call i32_add(1, %call i32_mul(2, 3))

# Run overloaded function
gleam run run examples/tao/02_overloaded_neg.tao
# Output: %fn<T>(x) -> %match T { | %I32 -> ... }

# Type-check a Tao program
gleam run check examples/tao/03_multiple_overloads.tao
# Output: ✓ Type checking examples/tao/03_multiple_overloads.tao
#         ✓ No errors found
```

### 📋 Next Steps

1. **Phase 1**: Complete type system (multiple patterns, constraints) - 1-2 weeks
2. **Phase 2**: More operators (comparison, unary, logical) - 1 week
3. **Phase 3**: Standard library (prelude, numeric hierarchy) - 2-3 weeks
4. **Phase 4**: Advanced features (pattern matching, let bindings) - 2-3 weeks
5. **Phase 5**: Test system (example-based tests) - 1-2 weeks

See **[10-overloading.md](./10-overloading.md)** for complete overloading specification.
See **[11-test-system.md](./11-test-system.md)** for test system specification.

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

### Implementation Plans

- **[00-tao-implementation.md](./00-tao-implementation.md)** - Implementation roadmap 📋 **NEW**
- **[13-stmt-system.md](./13-stmt-system.md)** - Stmt system design 📋 **NEW**
- **[12-import-system.md](./12-import-system.md)** - Import system specification ✅ **Complete**
- **[11-test-system.md](./11-test-system.md)** - Test system specification ✅ **Implemented**
- **[09-tao-mvp-plan.md](./09-tao-mvp-plan.md)** - MVP implementation plan ⏳
- **[06-implementation-plan.md](./06-implementation-plan.md)** - Full implementation plan

### Specifications

- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[07-desugaring-specification.md](./07-desugaring-specification.md)** - Detailed desugaring
- **[10-overloading-design.md](./10-overloading-design.md)** - Overloading design

### Related

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
