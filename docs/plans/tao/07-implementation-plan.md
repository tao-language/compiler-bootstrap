# Tao Implementation Plan

> **Goal**: Implement Tao language lexer, parser, and desugarer
> **Status**: 📋 Planning Complete, ⏳ Ready to Implement
> **Date**: March 2025

---

## Current Status

### ✅ Complete

**Tao AST** (`src/tao/ast.gleam`):
- ✅ All type definitions (Program, Declaration, Expr, Pattern, Type, etc.)
- ✅ Span tracking for all nodes
- ✅ Compiles successfully
- ⚠️ **No tests yet** - needs test suite

### ⏳ In Progress

**Nothing currently** - ready to start implementation

### 📋 Pending

| Component | File | Lines (est) | Tests (est) | Priority |
|-----------|------|-------------|-------------|----------|
| **Tao Lexer** | `src/tao/lexer.gleam` | ~400 | 50+ | 🔴 HIGH |
| **Tao Grammar** | `src/tao/grammar.gleam` | ~600 | 30+ | 🔴 HIGH |
| **Tao Desugarer** | `src/tao/desugar.gleam` | ~500 | 40+ | 🔴 HIGH |
| **Tao Formatter** | `src/tao/formatter.gleam` | ~300 | 20+ | 🟡 MEDIUM |
| **Core Changes** | `src/core/core.gleam` | ~100 | 20+ | 🟠 HIGH |
| **Integration Tests** | `test/tao/` | ~200 | 50+ | 🔴 HIGH |
| **Standard Library** | `src/tao/std/` | ~300 | 30+ | 🟡 MEDIUM |

---

## Phase 1: Core Language Changes (1-2 days)

**Why First**: Tao desugaring depends on these Core changes.

### 1.1 Add Pattern Guards to Core

**File**: `src/core/core.gleam`

**Change**:
```gleam
pub type Case {
  Case(
    pattern: Pattern,
    guard: Option(Term),  // NEW
    body: Term,
    span: Span,
  )
}
```

**Updates Needed**:
- [ ] Update `Case` type definition
- [ ] Update pattern matching evaluator
- [ ] Update exhaustiveness checking (conservative for guards)
- [ ] Add 20+ tests for guarded patterns

**Effort**: ~50 lines, 1 day
**Risk**: Low - additive change
**Tests**: Pattern guards, exhaustiveness with guards

---

### 1.2 Add Untyped Literals to Core

**File**: `src/core/core.gleam`

**Change**:
```gleam
pub type Literal {
  Int(Int)      // Untyped
  Float(Float)  // Untyped
}
```

**Current**:
```gleam
pub type Literal {
  I32(Int)
  I64(Int)
  U32(Int)
  U64(Int)
  F32(Float)
  F64(Float)
}
```

**Updates Needed**:
- [ ] Change `Literal` type
- [ ] Add `Coerce` term for type coercion
- [ ] Update type checker to insert coercions
- [ ] Update evaluator for coercion handling
- [ ] Update all literal construction sites
- [ ] Add 30+ tests for literal inference

**Effort**: ~100 lines, 1-2 days
**Risk**: Medium - changes many construction sites
**Tests**: Literal inference, coercion, type errors

---

## Phase 2: Tao Lexer (2-3 days)

**File**: `src/tao/lexer.gleam`

**Approach**: Base on `src/syntax/lexer.gleam`, add Tao-specific tokens

### 2.1 Token Types

```gleam
pub type TokenKind {
  // Literals
  IntLit
  FloatLit
  StringLit
  
  // Identifiers
  Ident        // lowercase, snake_case
  UpperIdent   // Uppercase, PascalCase (types, constructors)
  
  // Keywords
  Let, Mut, Fn, Type, Match, If, Else, Return
  Import, As, Do, Comptime
  
  // Operators
  Plus, Minus, Star, Slash, Percent
  Eq, EqEq, NotEq, Lt, Gt, Lte, Gte
  And, Or, Not
  Pipe, Arrow, FatArrow, Question, QuestionDot, LessMinus
  
  // Delimiters
  LParen, RParen, LBrace, RBrace, LBracket, RBracket
  Comma, Colon, Dot, Underscore
  
  // Comments (handled specially)
  LineComment, BlockComment
}
```

### 2.2 Implementation Tasks

- [ ] Copy `src/syntax/lexer.gleam` as base
- [ ] Add Tao-specific token kinds
- [ ] Handle keywords (let, mut, fn, type, etc.)
- [ ] Handle operators (<-, ?., ?, etc.)
- [ ] Handle identifiers (lowercase vs. Uppercase)
- [ ] Track positions for error reporting
- [ ] Write 50+ lexer tests

**Effort**: ~400 lines, 2-3 days
**Risk**: Low - based on proven lexer
**Tests**: Tokenization, positions, keywords, operators

---

## Phase 3: Tao Grammar (3-4 days)

**File**: `src/tao/grammar.gleam`

**Approach**: Use syntax library DSL

### 3.1 Grammar Structure

```gleam
pub fn tao_grammar() -> Grammar(ast.Program) {
  use g <- grammar.define
  
  g
  |> grammar.name("Tao")
  |> grammar.start("Program")
  
  // Tokens
  |> grammar.token("IntLit")
  |> grammar.token("FloatLit")
  // ... more tokens
  
  // Keywords
  |> grammar.keyword("let")
  |> grammar.keyword("fn")
  // ... more keywords
  
  // Rules
  |> grammar.rule("Program", [...])
  |> grammar.rule("Declaration", [...])
  |> grammar.rule("Expr", [...])
  // ... more rules
  
  // Operator precedence (10 levels)
  |> grammar.left_assoc("Expr", "Term", [...], 10)
}
```

### 3.2 Operator Precedence

| Level | Operators | Associativity |
|-------|-----------|---------------|
| 100 | `.`, `?.` | Left |
| 90 | `!` | Right |
| 80 | `*`, `/`, `%` | Left |
| 70 | `+`, `-` | Left |
| 60 | `<`, `>`, `<=`, `>=` | Left |
| 50 | `==`, `!=` | Left |
| 40 | `&&` | Left |
| 30 | `||` | Left |
| 20 | `<-` | Right |
| 10 | `\|>` | Left |

### 3.3 Implementation Tasks

- [ ] Define all grammar rules using syntax library DSL
- [ ] Set up 10 operator precedence levels
- [ ] Handle pattern matching syntax (OCaml style with `|`)
- [ ] Handle sum type layout (`type Maybe(a) = Some(a) | None`)
- [ ] Handle module syntax (import, as, names)
- [ ] Write 30+ parser tests
- [ ] Round-trip tests (parse → format → parse)

**Effort**: ~600 lines, 3-4 days
**Risk**: Low - reusing syntax library
**Tests**: Parsing, precedence, round-trips

---

## Phase 4: Tao Desugarer (3-4 days)

**File**: `src/tao/desugar.gleam`

**Approach**: Convert Tao AST → Core Term

### 4.1 Desugaring Rules

| Tao Construct | Core Desugaring |
|---------------|-----------------|
| `let x = e` | `Ann(e, type)` |
| `let mut x = e; x = x + 1` | SSA renaming: `x_0 = e; x_1 = x_0 + 1` |
| `fn add(a, b) { a + b }` | `Lam("a", Lam("b", App(App(Var("add"), Var("a")), Var("b"))))` |
| `a + b` | `App(App(Var("add"), a), b)` |
| `let x <- e1 in e2` | `App(App(Var("and_then"), e1), Lam("x", e2))` |
| `e?` | `Match(e, [Ok(x) -> x, Err(e) -> Err(e)])` |
| `user?.address` | `Match(user, [Some(u) -> u.address, None -> None])` |
| `do { mut x = 0; x = x + 1; x }` | Tail-recursive loop |
| `match x { \| Some(y) if y > 0 -> y }` | `Match(x, [Case(Some(y), Some(y > 0), y)])` |

### 4.2 Implementation Tasks

- [ ] Implement `desugar_program()`
- [ ] Implement `desugar_declaration()`
- [ ] Implement `desugar_expr()` for all 22 expression variants
- [ ] Implement `desugar_pattern()` for all 9 pattern variants
- [ ] Implement `desugar_type()`
- [ ] Handle operator overloading (name mangling)
- [ ] Handle mutable state threading (SSA renaming)
- [ ] Handle sugar expansion (`<-`, `?.`, `?`, `do { }`)
- [ ] Write 40+ desugaring tests
- [ ] Integration tests (Tao → Core → Type Check)

**Effort**: ~500 lines, 3-4 days
**Risk**: Medium - complex transformations
**Tests**: Each desugaring rule, integration

---

## Phase 5: Tao Formatter (2-3 days)

**File**: `src/tao/formatter.gleam`

**Approach**: Manual formatter using syntax formatter

### 5.1 Implementation Tasks

- [ ] Implement `format_program()`
- [ ] Implement `format_declaration()`
- [ ] Implement `format_expr()` with precedence-based parenthesization
- [ ] Implement `format_pattern()`
- [ ] Implement `format_type()`
- [ ] Layout hints for pretty-printing
- [ ] Write 20+ formatting tests
- [ ] Round-trip tests (parse → format → parse)

**Effort**: ~300 lines, 2-3 days
**Risk**: Low - manual but straightforward
**Tests**: Formatting, precedence, round-trips

---

## Phase 6: Integration Tests (2-3 days)

**Directory**: `test/tao/`

### 6.1 Test Structure

```
test/tao/
├── lexer_test.gleam       # 50+ tests
├── parser_test.gleam      # 30+ tests
├── desugar_test.gleam     # 40+ tests
├── formatter_test.gleam   # 20+ tests
└── integration_test.gleam # 50+ tests
```

### 6.2 Integration Test Examples

```gleam
// Tao source → Core → Type Check → Evaluate
pub fn tao_add_test() {
  let source = "let add = fn(a, b) { a + b } in add(1, 2)"
  let ast = parse_tao(source)
  let core_term = desugar_tao(ast)
  let #(value, type_) = type_check(core_term)
  value |> should.equal(VLit(Int(3)))
}

// Sugar expansion
pub fn tao_bind_operator_test() {
  let source = "let x <- result in x + 1"
  let ast = parse_tao(source)
  let core_term = desugar_tao(ast)
  // Should desugar to: and_then(result, fn(x) { x + 1 })
  core_term |> should.match_pattern(App(App(Var("and_then"), ...), ...))
}
```

**Effort**: ~200 lines, 2-3 days
**Risk**: Low - straightforward testing
**Tests**: End-to-end, sugar expansion, error cases

---

## Phase 7: Standard Library (3-4 days)

**Directory**: `src/tao/std/`

### 7.1 Module Structure

```
src/tao/std/
├── maybe.gleam      # Maybe type (Some, None)
├── result.gleam     # Result type (Ok, Err)
├── list.gleam       # List type and operations
├── option.gleam     # Option combinators (map, and_then, etc.)
└── prelude.gleam    # Auto-imported basics
```

### 7.2 Implementation Tasks

- [ ] Implement `Maybe` type and combinators
- [ ] Implement `Result` type and combinators
- [ ] Implement `List` type and operations
- [ ] Implement `Option` combinators
- [ ] Implement `Result` combinators
- [ ] Write 30+ standard library tests

**Effort**: ~300 lines, 3-4 days
**Risk**: Low - straightforward implementations
**Tests**: Each combinator, edge cases

---

## Timeline Summary

| Phase | Component | Days | Tests | Dependencies |
|-------|-----------|------|-------|--------------|
| 1 | Core Changes | 1-2 | 20+ | None |
| 2 | Tao Lexer | 2-3 | 50+ | Phase 1 |
| 3 | Tao Grammar | 3-4 | 30+ | Phase 2 |
| 4 | Tao Desugarer | 3-4 | 40+ | Phase 1, 3 |
| 5 | Tao Formatter | 2-3 | 20+ | Phase 3 |
| 6 | Integration Tests | 2-3 | 50+ | Phase 4, 5 |
| 7 | Standard Library | 3-4 | 30+ | Phase 4 |
| **Total** | | **16-23 days** | **240+** | |

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Core changes break existing code | Low | High | Extensive test suite (401 tests) |
| Lexer edge cases | Low | Low | Base on proven syntax lexer |
| Grammar ambiguity | Low | Medium | LL(1) design, no backtracking |
| Desugaring bugs | Medium | High | Extensive tests, integration tests |
| Scope creep | Medium | Medium | Stick to MVP, enhance later |

---

## Success Criteria

**After completion**:
- ✅ Can write Tao source files
- ✅ Tao compiles to Core
- ✅ Core type checks and evaluates
- ✅ Basic standard library works
- ✅ 240+ tests passing
- ✅ Documentation with examples

**Metrics**:
- 0 warnings
- 240+ tests passing
- Example programs compile and run
- Error messages are helpful

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview
- **[02-syntax.md](./02-syntax.md)** - Tao syntax specification
- **[03-desugaring.md](./03-desugaring.md)** - Desugaring rules
- **[05-comprehensive-analysis.md](./05-comprehensive-analysis.md)** - Comprehensive analysis
- **[../../docs/core.md](../../docs/core.md)** - Core language semantics
- **[../../syntax-library.md](../../syntax-library.md)** - Syntax library usage

---

## Next Steps

1. **Start with Phase 1** - Core language changes (pattern guards, untyped literals)
2. **Then Phase 2** - Tao lexer (based on syntax lexer)
3. **Then Phase 3** - Tao grammar (using syntax library DSL)
4. **Then Phase 4** - Tao desugarer (AST → Core)
5. **Then Phase 5-7** - Formatter, tests, standard library

**Ready to start?** Begin with Phase 1 (Core changes) this week.
