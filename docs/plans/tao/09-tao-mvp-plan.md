# Tao MVP Implementation Plan

> **Goal**: Minimal viable Tao that compiles to Core and runs end-to-end
> **Status**: ⏳ **Starting Implementation** - March 2026
> **Target**: 2-3 weeks for MVP

---

## Core Insight

**Get end-to-end working first, then expand.** A minimal working Tao validates the entire architecture and unblocks everything else.

---

## MVP Scope (Minimal Viable)

### What's IN Scope ✅

| Feature | Description | Priority |
|---------|-------------|----------|
| **Functions** | `fn add(x: Int, y: Int): Int { x + y }` | 🔴 P0 |
| **Let bindings** | `let x = 5` | 🔴 P0 |
| **Pattern matching** | `match x { | Some(y) -> y | None -> 0 }` | 🔴 P0 |
| **Basic types** | `Int`, `Bool`, `String` | 🔴 P0 |
| **Function calls** | `add(1, 2)` | 🔴 P0 |
| **Operators** | `+`, `-`, `*`, `/`, `==`, `!=` | 🔴 P0 |
| **If expressions** | `if cond { a } else { b }` | 🟡 P1 |
| **Type annotations** | `let x: Int = 5` | 🟡 P1 |

### What's OUT Scope ❌ (For Now)

| Feature | Why Deferred |
|---------|--------------|
| Mutable variables | Can use Core directly initially |
| Do blocks | Desugaring complexity |
| Imports/modules | Use single-file programs first |
| Generics | Core handles polymorphism |
| Advanced types | Dependent types via Core |
| Standard library | Build after MVP works |

---

## Architecture

### Module Structure (MVP)

```
src/
├── tao/
│   ├── ast.gleam              # ✅ Already complete
│   ├── lexer.gleam            # ⏳ TODO (~300 lines)
│   ├── grammar.gleam          # ⏳ TODO (~400 lines)
│   └── desugar.gleam          # ⏳ TODO (~300 lines)
├── syntax/                    # ✅ Reuse existing
└── core/                      # ✅ Reuse existing
```

### Compilation Pipeline (MVP)

```
Tao Source (.tao)
    ↓
Tao Lexer (tokenize)
    ↓
Tao Parser (syntax library + tao grammar)
    ↓
Tao AST
    ↓
Tao Desugarer (Tao AST → Core Term)
    ↓
Core Term
    ↓
Core Type Checker + Evaluator
    ↓
Result
```

---

## Implementation Phases

### Phase 1: Foundation (Week 1)

**Goal**: Lexer + Parser working

#### Day 1-2: Tao Lexer
- [ ] Tokenize identifiers, keywords, literals
- [ ] Handle operators (`+`, `-`, `*`, `/`, etc.)
- [ ] Handle comments (`//`, `/* */`)
- [ ] Track source positions
- [ ] 30+ lexer tests

**File**: `src/tao/lexer.gleam`

#### Day 3-5: Tao Grammar
- [ ] Define grammar using syntax library
- [ ] Parse functions, let bindings, expressions
- [ ] Parse pattern matching
- [ ] Handle operator precedence
- [ ] 40+ parser tests

**File**: `src/tao/grammar.gleam`

**Deliverable**: Can parse Tao source to Tao AST

---

### Phase 2: Desugaring (Week 2)

**Goal**: Tao → Core compilation working

#### Day 1-3: Basic Desugaring
- [ ] Functions → Core lambdas
- [ ] Let bindings → Core let
- [ ] Literals → Core literals
- [ ] Variables → Core variables
- [ ] 30+ desugarer tests

#### Day 4-5: Operators + Match
- [ ] Operators → Core FFI calls (`%call i32_add`)
- [ ] Pattern matching → Core `%match`
- [ ] If expressions → Core match
- [ ] Integration tests

**File**: `src/tao/desugar.gleam`

**Deliverable**: Can compile Tao to Core terms

---

### Phase 3: Integration (Week 3)

**Goal**: End-to-end working

#### Day 1-2: CLI Integration
- [ ] Wire Tao parser into CLI
- [ ] Wire Tao desugarer into CLI
- [ ] File type detection (`.tao` extension)
- [ ] Error reporting for Tao

**File**: `src/compiler_bootstrap.gleam`

#### Day 3-4: Examples + Tests
- [ ] 5-10 Tao example programs
- [ ] End-to-end tests
- [ ] Golden file tests
- [ ] Documentation

**Files**: `examples/tao/*.tao`, `test/tao/`

#### Day 5: Polish + Bug Fixes
- [ ] Fix issues found during testing
- [ ] Improve error messages
- [ ] Update documentation

**Deliverable**: `gleam run run examples/tao/hello.tao` works!

---

## Success Criteria

### MVP Complete When:

- ✅ Can write a Tao function and run it
- ✅ Tao pattern matching works
- ✅ Tao operators compile to Core FFI calls
- ✅ Error messages work for Tao programs
- ✅ 400+ tests passing (including Tao tests)
- ✅ 5+ working Tao example programs

### Example Programs (MVP)

```tao
// examples/tao/01_hello.tao
fn main() {
  print("Hello, Tao!")
}
```

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

## Technical Decisions

### 1. Reuse Syntax Library

**Decision**: Use existing `syntax/` library for Tao parsing

**Rationale**:
- Already tested and working
- Provides error reporting for free
- Consistent with Core parsing
- No need to reinvent

**Implementation**:
```gleam
// tao/grammar.gleam
pub fn tao_grammar() -> Grammar(Program) {
  use g <- grammar.define
  g
  |> grammar.name("Tao")
  |> grammar.start("Program")
  // ... define Tao grammar
}

pub fn parse(source: String) -> ParseResult(Program) {
  grammar.parse(tao_grammar(), source, error_program)
}
```

---

### 2. Desugarer Architecture

**Decision**: Tao AST → Core Term transformation

**Rationale**:
- Clean separation of concerns
- Tao can evolve independently
- Core stays minimal
- Easy to debug (see generated Core)

**Implementation**:
```gleam
// tao/desugar.gleam
pub fn desugar_program(prog: tao.ast.Program) -> core.core.Term {
  // Transform Tao to Core
  case prog {
    tao.ast.Program(decls) -> {
      // Convert each declaration
      core.core.Let(..., desugar_expr(expr), ...)
    }
  }
}
```

---

### 3. Operator Desugaring

**Decision**: Operators → Core FFI calls

**Rationale**:
- Core already has FFI (`%call i32_add`)
- Type-directed desugaring
- No operator overloading complexity in MVP

**Implementation**:
```gleam
// Tao source
let x = a + b

// Desugars to Core
%call i32_add(a, b)
```

---

### 4. Pattern Matching Desugaring

**Decision**: Tao match → Core `%match`

**Rationale**:
- Core already has exhaustive matching
- Same semantics
- Direct translation

**Implementation**:
```gleam
// Tao
match opt {
  | Some(x) -> x
  | None -> 0
}

// Core
%match opt ~ motive {
  | #Some(x) -> x
  | #None -> 0
}
```

---

## Risk Mitigation

### Risk 1: Scope Creep

**Mitigation**:
- Stick to MVP features only
- Defer "nice to have" features
- Get end-to-end working first

### Risk 2: Desugaring Complexity

**Mitigation**:
- Start with simple cases
- Add complexity incrementally
- Test each desugaring rule

### Risk 3: Type System Mismatch

**Mitigation**:
- Keep Tao types simple for MVP
- Use Core for advanced types
- Document limitations clearly

---

## Testing Strategy

### Unit Tests

```gleam
// test/tao/lexer_test.gleam
pub fn tokenize_function_test() {
  tokenize("fn add(x: Int): Int { x }")
  |> should.equal([...])
}

// test/tao/parser_test.gleam
pub fn parse_function_test() {
  parse("fn add(x: Int): Int { x }")
  |> should.equal(Program(...))
}

// test/tao/desugar_test.gleam
pub fn desugar_function_test() {
  desugar(tao_function)
  |> should.equal(core_lambda)
}
```

### Integration Tests

```gleam
// test/tao/integration_test.gleam
pub fn factorial_integration_test() {
  run_tao("examples/tao/factorial.tao")
  |> should.equal(120)
}
```

### Golden File Tests

```bash
# examples/tao/factorial.tao
fn factorial(n: Int): Int {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}

# examples/tao/factorial.output.txt
120
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[07-desugaring-specification.md](./07-desugaring-specification.md)** - Detailed desugaring
- **[../../docs/core-syntax.md](../../docs/core-syntax.md)** - Core syntax reference
- **[../../docs/syntax-library.md](../../docs/syntax-library.md)** - Syntax library

---

## References

- [Tao AST](../../src/tao/ast.gleam) - Already complete ✅
- [Syntax Library](../../src/syntax/grammar.gleam) - Reuse for parsing
- [Core Language](../../src/core/core.gleam) - Compilation target
- [CLI](../../src/compiler_bootstrap.gleam) - Integration point

---

## Timeline

| Week | Focus | Deliverable |
|------|-------|-------------|
| **Week 1** | Lexer + Parser | Can parse Tao to AST |
| **Week 2** | Desugarer | Can compile Tao → Core |
| **Week 3** | Integration | End-to-end working |

**Total**: 2-3 weeks for MVP

---

**Let's build Tao! 🚀**
