# Tao MVP Implementation Plan

> **Goal**: Minimal viable Tao that compiles to Core and runs end-to-end
> **Status**: ✅ **COMPLETE** - All MVP features implemented and tested
> **Date**: March 2026

---

## Implementation Summary

### ✅ Complete Features

| Feature | Status | Description |
|---------|--------|-------------|
| **Lexer** | ✅ Complete | Tokenizes identifiers, numbers, operators |
| **Parser** | ✅ Complete | Expressions with correct precedence |
| **Formatter** | ✅ Complete | Formats expressions back to source |
| **Desugarer** | ✅ Complete | Tao → Core transformation |
| **CLI Integration** | ✅ Complete | `gleam run run/check file.tao` |
| **Examples** | ✅ Complete | 2 working examples |
| **Tests** | ✅ Complete | 39 tests passing |

### MVP Features Implemented

- ✅ Numbers: `42`
- ✅ Variables: `x`
- ✅ Arithmetic: `+`, `-`, `*`, `/`
- ✅ Correct precedence: `*` binds tighter than `+`
- ✅ Left associativity
- ✅ Parentheses: `(1 + 2) * 3`
- ✅ Desugaring: `x + y` → `%call i32_add(x, y)`
- ✅ Type checking via Core
- ✅ Evaluation via Core
- ✅ Clean output (no "Result: " prefix)

### Test Results

| Metric | Value |
|--------|-------|
| **Total Tests** | **406** |
| **Tao Tests** | **39** (24 syntax + 15 desugar) |
| **Test Failures** | **0** |

---

## Completed Phases

### Phase 1: Foundation ✅ (Week 1)

**Goal**: Lexer + Parser working

#### Day 1-2: Tao Lexer ✅
- ✅ Tokenize identifiers, keywords, numbers
- ✅ Handle operators (`+`, `-`, `*`, `/`)
- ✅ Handle comments (`//`, `/* */`)
- ✅ Track source positions
- ✅ **File**: `src/tao/lexer.gleam`

#### Day 3-5: Tao Grammar ✅
- ✅ Define grammar using syntax library
- ✅ Parse expressions
- ✅ Handle operator precedence
- ✅ **File**: `src/tao/syntax.gleam`
- ✅ **Tests**: 24 syntax tests

**Deliverable**: ✅ Can parse Tao source to Tao AST

---

### Phase 2: Desugarer ✅ (Week 2)

#### Day 1-3: Basic Desugaring ✅
- ✅ Numbers → Core literals
- ✅ Variables → Core variables
- ✅ **File**: `src/tao/desugar.gleam`

#### Day 4-5: Operators ✅
- ✅ Operators → Core FFI calls
- ✅ `x + y` → `%call i32_add(x, y)`
- ✅ **Tests**: 15 desugar tests

**Deliverable**: ✅ Can compile Tao to Core terms

---

### Phase 3: Integration ✅ (Week 3)

#### Day 1-2: CLI Integration ✅
- ✅ Wire Tao parser into CLI
- ✅ Wire Tao desugarer into CLI
- ✅ File type detection (`.tao` extension)
- ✅ **File**: `src/compiler_bootstrap.gleam`

#### Day 3-4: Examples + Tests ✅
- ✅ 2 Tao example programs
- ✅ End-to-end tests
- ✅ Golden file tests

#### Day 5: Polish ✅
- ✅ Remove "Result: " prefix for clean output
- ✅ Update documentation

**Deliverable**: ✅ `gleam run run examples/tao/01_arithmetic.tao` works!

---

## Example Programs

### Arithmetic (`examples/tao/01_arithmetic.tao`)

```tao
// Tao source
1 + 2
```

```bash
# Run
gleam run run examples/tao/01_arithmetic.tao

# Output
%call i32_add(1, 2)
```

### Precedence (`examples/tao/02_precedence.tao`)

```tao
// Tao source
1 + 2 * 3
```

```bash
# Run
gleam run run examples/tao/02_precedence.tao

# Output
%call i32_add(1, %call i32_mul(2, 3))
```

---

## Files Created

| File | Description | Lines |
|------|-------------|-------|
| `src/tao/lexer.gleam` | Tao lexer wrapper | 84 |
| `src/tao/syntax.gleam` | Tao grammar & parser | 227 |
| `src/tao/desugar.gleam` | Tao → Core desugarer | 141 |
| `test/tao/syntax_test.gleam` | Parser tests | 217 |
| `test/tao/desugar_test.gleam` | Desugarer tests | 154 |
| `docs/tao-syntax.md` | Tao syntax tutorial | 200+ |
| `docs/plans/tao/09-tao-mvp-plan.md` | This plan | - |
| `examples/tao/*.tao` | Tao examples | 2 files |

---

## Next Steps (Post-MVP)

### Phase 4: Expand Grammar (1-2 weeks)

- [ ] Function calls: `add(1, 2)`
- [ ] Let bindings: `let x = 5`
- [ ] Function definitions: `fn f(x) { x }`
- [ ] Pattern matching: `match x { ... }`
- [ ] If expressions: `if cond { a } else { b }`

### Phase 5: Type System (2-3 weeks)

- [ ] Type annotations
- [ ] Type inference
- [ ] Sum types
- [ ] Pattern matching with GADTs

### Phase 6: Standard Library (2-3 weeks)

- [ ] Prelude (Bool, Option, Result)
- [ ] Basic operations
- [ ] Import system

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Tao language overview (updated with MVP status)
- **[../../docs/tao-syntax.md](../../docs/tao-syntax.md)** - Tao syntax tutorial
- **[../../docs/core-syntax.md](../../docs/core-syntax.md)** - Core syntax reference
- **[../../docs/cli.md](../../docs/cli.md)** - CLI documentation

---

## References

- [Tao Lexer](../../src/tao/lexer.gleam)
- [Tao Syntax](../../src/tao/syntax.gleam)
- [Tao Desugarer](../../src/tao/desugar.gleam)
- [Tao Tests](../../test/tao/)
- [CLI](../../src/compiler_bootstrap.gleam)

---

**Tao MVP is COMPLETE! 🎉**
