# Tao Language Overview

> **Goal**: Simple, pragmatic functional language with dependent types—TypeScript-like syntax without the complexity
> **Status**: 📋 Designed, ⏳ Implementation planning
> **Date**: March 2025

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

## Architecture

### Module Structure

```
src/
├── tao/
│   ├── lexer.gleam        # Tao tokenizer (~400 lines) ← TODO
│   ├── grammar.gleam      # Tao grammar definition (~600 lines) ← TODO
│   ├── parser.gleam       # Thin wrapper: syntax.parse(tao_grammar(), src) ← TODO
│   ├── formatter.gleam    # Manual formatter using syntax formatter ← TODO
│   └── desugar.gleam      # Tao AST → Core Term (~500 lines) ← TODO
├── syntax/                # Reuse existing syntax library
│   ├── grammar.gleam      # Grammar DSL (~786 lines) ✅
│   ├── lexer.gleam        # Tokenizer (~400 lines) ✅
│   └── formatter.gleam    # Document algebra (~139 lines) ✅
└── core/                  # Reuse existing core language
    └── core.gleam         # Type checker, evaluator, unifier (~1800 lines) ✅
```

### Compilation Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│  Tao Source (.tao)                                              │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│  Lexer (src/tao/lexer.gleam)                                    │
│  - Tokenize: identifiers, keywords, operators, literals         │
│  - Handle: comments, strings, numbers                           │
│  - Track: positions for error reporting                         │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│  Parser (src/tao/grammar.gleam + syntax library)                │
│  - Parse: Tao AST with type annotations                         │
│  - Handle: operator precedence, pattern matching                │
│  - Return: TaoAst + errors                                      │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│  Desugar (src/tao/desugar.gleam)                                │
│  - Convert: Tao AST → Core Term                                 │
│  - Inject: Type applications for overloaded operators           │
│  - Thread: Explicit state for mutable variables                 │
│  - Expand: `<-`, `?.`, `?` sugar to core operations             │
└─────────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────────┐
│  Core Language (src/core/core.gleam)                            │
│  - Type check: Bidirectional (infer/check)                      │
│  - Normalize: Normalization by evaluation                       │
│  - Evaluate: With FFI/comptime support                          │
│  - Return: Typed Core Term + errors                             │
└─────────────────────────────────────────────────────────────────┘
```

---

## Design Principles

### 1. Immutable by Default (Rust/OCaml Model)

```tao
let x = 5           // Immutable
let mut y = 0       // Explicit mutability
y = y + 1           // OK
```

**Desugaring**: Mutable variables become explicit state threading in core.

### 2. No OOP / No Inheritance

```tao
// ❌ No classes
// class Animal { ... }  // NOT ALLOWED

// ✅ Plain records
type Animal = {
  name: String,
  age: I32,
}

// ✅ Functions operate on data
fn get_name(animal: Animal) -> String {
  animal.name
}
```

**Desugaring**: Records map directly to core `Rcd`, functions to core `Lam`.

### 3. GADTs with Full Pattern Matching

```tao
type Vec(n: Nat, a: Type) {
  Nil: Vec(0, a)
  Cons: (n: Nat, a, Vec(n, a)) -> Vec(n + 1, a)
}

fn head(v: Vec(n, a)) -> Maybe(a) {
  match v {
    Nil => None
    Cons(_, x, _) => Some(x)
  }
}
```

**Desugaring**: GADTs map to core `Ctr` with `ret_ty`. Match maps to core `Match`.

### 4. Dependent Types with Inference

```tao
// 99% case: Simple types
fn add(a: I32, b: I32) -> I32 { a + b }

// 1% case: Full dependent types
fn matmul(a: Matrix(m, n), b: Matrix(n, p)) -> Matrix(m, p) {
  // Type checker verifies dimensions
}
```

**Desugaring**: Type annotations are optional sugar. Type inference injects explicit types.

### 5. No Async/Await

```tao
// ❌ No async/await
// async fn fetch() { ... }  // NOT ALLOWED

// ✅ Just functions
fn fetch_data(url: String) -> Result(String, Error) {
  // Implementation detail: blocking or non-blocking
}
```

**Desugaring**: All functions are core `Lam`. Effects handled by FFI/permissions.

### 6. No NULL, Use Maybe

```tao
// ❌ No null
// let x: String = null  // NOT ALLOWED

// ✅ Maybe type
type Maybe(a) { Some(a), None }

// ✅ Optional chaining
let name = user?.name  // Maybe(String)
```

**Desugaring**: `?.` expands to nested `match` expressions.

### 7. Result-Based Error Handling

```tao
// ❌ No try/catch

// ✅ Result with bind operator
fn process() -> Result(I32, String) {
  let x <- parse_int("42")  // Unwraps Ok, returns early on Err
  let y <- parse_int("10")
  Ok(x + y)
}

// ✅ Optional chaining
let value = result?  // Unwraps Ok, returns early on Err
```

**Desugaring**: `<-` expands to `and_then`/`flat_map`. `?` expands to `match`.

### 8. No IO Monad (Pragmatic Effects)

```tao
// ✅ Pure built-ins
let x = 5 + 3  // i32_add(5, 3)

// ✅ Effects return Result
fn read_file(path: String) -> Result(String, Error)

// ✅ Permission attributes
@permission(Read("/tmp"))
fn read_temp() -> Result(String, Error) {
  read_file("/tmp/data.txt")
}
```

**Desugaring**: Attributes are metadata. Effects handled by core FFI/permissions.

### 9. Operator Overloading via Type Inference

```tao
// ✅ Operators predefined, cannot create new ones
// Allowed: +, -, *, /, ==, !=, <, >, <=, >=, &&, ||, !

// ✅ Overloading via pattern matching
fn add(a: I32, b: I32) -> I32 { i32_add(a, b) }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }
fn add(a: Vec3, b: Vec3) -> Vec3 { vec3_add(a, b) }

// ✅ Type inference injects type applications
let x = 5 + 3      // Desugars: add(I32, 5, 3)
let y = 5.0 + 3.0  // Desugars: add(F64, 5.0, 3.0)
```

**Desugaring**: NbE resolves overloaded functions at compile-time.

---

## Implementation Status

### ✅ Complete and Working (Core Infrastructure)

**Syntax Library** (`src/syntax/`):
- Lexer (~400 lines) - Tokenizes identifiers, keywords, numbers, strings, comments
- Grammar DSL (~786 lines) - Full layout-aware grammar definition
- Formatter (~139 lines) - Document algebra with best-fit rendering
- Calculator example - Working parser/formatter demonstration

**Core Language** (`src/core/`):
- Term types - Var, Lam, App, Pi, Rcd, Match, Ctr, Hole, Lit, Ann, Call, Comptime
- Value types - Normalization by evaluation
- Type checker - Bidirectional type checking (infer/check)
- Unifier - Type unification with occurs check
- FFI/Comptime - Compile-time evaluation with permissions
- Exhaustiveness checking - Maranget's algorithm
- **263 tests passing**

### ⏳ In Progress (Tao Language)

**Phase 1: Lexer** (`src/tao/lexer.gleam`):
- [ ] Tokenize identifiers (lowercase, Uppercase)
- [ ] Tokenize keywords (let, mut, fn, type, match, etc.)
- [ ] Tokenize literals (I32, I64, F32, F64, String, Bool)
- [ ] Tokenize operators (+, -, *, /, ==, !=, etc.)
- [ ] Handle comments (line `//`, block `/* */`)
- [ ] Track positions for error reporting

**Phase 2: Grammar** (`src/tao/grammar.gleam`):
- [ ] Define Tao AST types
- [ ] Define grammar rules using syntax library
- [ ] Handle operator precedence
- [ ] Handle pattern matching syntax
- [ ] Handle type annotations (optional)
- [ ] Handle attributes (@permission, @effect, etc.)

**Phase 3: Parser** (`src/tao/parser.gleam`):
- [ ] Thin wrapper around syntax library parser
- [ ] Error handling and reporting
- [ ] Source location tracking

**Phase 4: Formatter** (`src/tao/formatter.gleam`):
- [ ] Manual formatter for Tao AST
- [ ] Precedence-based parenthesization
- [ ] Layout hints for pretty-printing

**Phase 5: Desugaring** (`src/tao/desugar.gleam`):
- [ ] Convert Tao AST → Core Term
- [ ] Type inference and injection
- [ ] Operator overloading resolution (NbE)
- [ ] Mutable variable state threading
- [ ] Expand `<-` bind operator
- [ ] Expand `?.` optional chaining
- [ ] Expand `?` Result unwrap
- [ ] Handle attributes (permissions, effects)

**Phase 6: Standard Library** (`src/tao/std/`):
- [ ] Maybe type (Some, None)
- [ ] Result type (Ok, Err)
- [ ] List type and operations
- [ ] Option combinators (map, and_then, etc.)
- [ ] Result combinators
- [ ] Common utilities

### 📋 Planned (Future Enhancements)

- Module system (import/export)
- Package manager
- LSP support (autocomplete, go-to-definition, etc.)
- Documentation generator
- Performance optimizations
- Additional standard library modules

---

## Key Concepts

### 1. Type Inference with NbE Resolution

Type inference injects explicit type applications during normalization:

```tao
// Source
fn add(a: I32, b: I32) -> I32 { a + b }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }

let x = 5 + 3  // Inferred: I32

// Desugared (core)
let x = add(I32, 5, 3)  // Type application injected
```

**How it works**:
1. Parse Tao AST
2. Type check (bidirectional)
3. During NbE, resolve overloaded functions by matching argument types
4. Inject type applications in core Term

### 2. Mutable Variable State Threading

```tao
// Tao source
let mut counter = 0
counter = counter + 1
counter = counter * 2

// Desugared to core (explicit state)
let counter_0 = 0
let counter_1 = counter_0 + 1
let counter_2 = counter_1 * 2
// Use counter_2 from here on
```

**How it works**:
1. Track mutable variables in desugarer
2. Generate fresh names for each assignment
3. Thread state explicitly through computations

### 3. Bind Operator (`<-`) Expansion

```tao
// Tao source
fn process() -> Result(I32, String) {
  let x <- parse_int("42")
  let y <- parse_int("10")
  Ok(x + y)
}

// Desugared to core
fn process() -> Result(I32, String) {
  and_then(parse_int("42"), fn(x) {
    and_then(parse_int("10"), fn(y) {
      Ok(x + y)
    })
  })
}
```

**How it works**:
1. Identify `<-` expressions in function body
2. Convert to chained `and_then` calls
3. Wrap final expression in appropriate constructor

### 4. Optional Chaining (`?.`) Expansion

```tao
// Tao source
let city = user?.address?.city

// Desugared to core
let city = match user {
  Some(u) => match u.address {
    Some(addr) => Some(addr.city)
    None => None
  }
  None => None
}
```

**How it works**:
1. Identify `?.` chains
2. Generate nested `match` expressions
3. Return `None` at first `None`, `Some(value)` at end

---

## File Structure

```
src/
├── tao/
│   ├── lexer.gleam        # Tao tokenizer ← TODO
│   ├── grammar.gleam      # Tao grammar definition ← TODO
│   ├── parser.gleam       # Parser wrapper ← TODO
│   ├── formatter.gleam    # Tao formatter ← TODO
│   ├── desugar.gleam      # Tao → Core desugaring ← TODO
│   └── std/
│       ├── maybe.gleam    # Maybe type (Some, None) ← TODO
│       ├── result.gleam   # Result type (Ok, Err) ← TODO
│       └── list.gleam     # List type and operations ← TODO
├── syntax/                # Reuse existing
│   ├── grammar.gleam      # Grammar DSL (~786 lines) ✅
│   ├── lexer.gleam        # Tokenizer (~400 lines) ✅
│   └── formatter.gleam    # Document algebra (~139 lines) ✅
└── core/                  # Reuse existing
    └── core.gleam         # Type checker, evaluator (~1800 lines) ✅
```

---

## Related Documents

- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules to core language
- **[04-standard-library.md](./04-standard-library.md)** - Standard library design
- **[../grammar/01-overview.md](../grammar/01-overview.md)** - Grammar system overview
- **[../core/01-overview.md](../core/01-overview.md)** - Core language overview

---

## References

- [Syntax Library](../../src/syntax/grammar.gleam)
- [Core Language](../../src/core/core.gleam)
- [Tao Language Design](../../docs/plans/tao/01-overview.md)
- [Learn Tao in Y Minutes](../../docs/plans/tao/02-syntax.md#learn-tao-in-y-minutes)
