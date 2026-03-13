# Tao MVP Implementation

> **Status**: ⏳ **In Progress** - Week 1 (Lexer + Parser)
> **Started**: March 2026
> **Target**: 2-3 weeks

---

## Directory Structure

```
src/tao/
├── ast.gleam              # ✅ Tao AST (already complete)
├── lexer.gleam            # ⏳ TODO - Tokenizer
├── grammar.gleam          # ⏳ TODO - Parser using syntax library
└── desugar.gleam          # ⏳ TODO - Tao → Core transformation
```

```
examples/tao/              # ⏳ TODO - Tao example programs
├── 01_hello.tao
├── 02_factorial.tao
└── 03_option.tao
```

```
test/tao/                  # ⏳ TODO - Tao tests
├── lexer_test.gleam
├── grammar_test.gleam
├── desugar_test.gleam
└── integration_test.gleam
```

---

## Implementation Checklist

### Week 1: Lexer + Parser

#### Tao Lexer (`src/tao/lexer.gleam`)
- [ ] Tokenize identifiers
- [ ] Tokenize keywords (`fn`, `let`, `match`, `if`, `else`, `type`)
- [ ] Tokenize literals (integers, floats, strings, bools)
- [ ] Tokenize operators (`+`, `-`, `*`, `/`, `==`, `!=`, `<`, `>`)
- [ ] Handle comments (`//`, `/* */`)
- [ ] Track source positions
- [ ] 30+ lexer tests

#### Tao Grammar (`src/tao/grammar.gleam`)
- [ ] Define grammar using syntax library
- [ ] Parse functions
- [ ] Parse let bindings
- [ ] Parse expressions (literals, variables, operators)
- [ ] Parse pattern matching
- [ ] Handle operator precedence
- [ ] 40+ parser tests

**Deliverable**: Can parse Tao source to Tao AST

---

### Week 2: Desugarer

#### Tao Desugarer (`src/tao/desugar.gleam`)
- [ ] Functions → Core lambdas
- [ ] Let bindings → Core let
- [ ] Literals → Core literals
- [ ] Variables → Core variables
- [ ] Operators → Core FFI calls
- [ ] Pattern matching → Core %match
- [ ] If expressions → Core match
- [ ] 30+ desugarer tests

**Deliverable**: Can compile Tao to Core terms

---

### Week 3: Integration

#### CLI Integration (`src/compiler_bootstrap.gleam`)
- [ ] Wire Tao parser into CLI
- [ ] Wire Tao desugarer into CLI
- [ ] File type detection (`.tao` extension)
- [ ] Error reporting for Tao

#### Examples + Tests
- [ ] 5-10 Tao example programs
- [ ] End-to-end tests
- [ ] Golden file tests
- [ ] Documentation

**Deliverable**: `gleam run run examples/tao/hello.tao` works!

---

## Quick Start (When Complete)

```bash
# Run a Tao program
gleam run run examples/tao/hello.tao

# Type-check a Tao file
gleam run check examples/tao/factorial.tao

# Run Tao tests
gleam test
```

---

## Example Tao Programs

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

- **[../../docs/plans/tao/09-tao-mvp-plan.md](../../docs/plans/tao/09-tao-mvp-plan.md)** - MVP implementation plan
- **[../../docs/plans/tao/01-overview.md](../../docs/plans/tao/01-overview.md)** - Tao language overview
- **[../../docs/core-syntax.md](../../docs/core-syntax.md)** - Core syntax reference
- **[../../docs/syntax-library.md](../../docs/syntax-library.md)** - Syntax library

---

## References

- [Tao AST](../../src/tao/ast.gleam)
- [Syntax Library](../../src/syntax/grammar.gleam)
- [Core Language](../../src/core/core.gleam)
- [CLI](../../src/compiler_bootstrap.gleam)

---

**Let's build Tao! 🚀**
