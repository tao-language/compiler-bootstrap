# Testing Plans Overview

> **Goal**: End-to-end testing infrastructure for the compiler
> **Status**: ✅ E2E tests complete, Error improvements complete
> **Date**: March 11, 2026

---

## Core Principle

**Examples are living documentation.** Every example in `examples/` should:
1. Demonstrate a specific language feature or error case
2. Be tested automatically with golden file comparison
3. Match exact CLI output (what you see is what you get)

---

## Architecture

### Test System Overview

```
examples/
├── core/                    # Core language examples
│   ├── programs/            # Successful programs
│   ├── terms/               # Individual term examples
│   └── errors/              # Error cases
│       ├── type_errors/
│       ├── syntax_errors/
│       ├── syntax_recovery/
│       └── exhaustiveness_checks/
└── tao/                     # Tao language examples (future)
    ├── programs/
    └── errors/
```

### Test Execution Flow

```
Example (.core.tao)
    ↓
Read source file
    ↓
Parse → Type Check → Evaluate
    ↓
Format Output (CLI format)
    ↓
Compare with Golden (.output.txt)
    ↓
Pass/Fail
```

---

## Design Principles

1. **Golden files = CLI output** - What you see running the CLI is what goes in golden files
2. **Test failures show diffs** - Clear before/after comparison for debugging
3. **Auto-discovery** - New examples automatically picked up by tests
4. **Category-based** - Different directories = different expectations (success vs error)
5. **Error resilience** - Tests continue even if some examples fail

---

## Implementation Status

### ✅ Complete and Working

**E2E Test Infrastructure** (`test/core/examples_test.gleam`):
- ✅ Auto-discovery of all `.core.tao` files
- ✅ Category-based test grouping (programs, terms, errors/*)
- ✅ Golden file comparison with `normalize_output()`
- ✅ Detailed failure messages with expected vs actual
- ✅ **376 tests passing**

**Error Message Improvements** (`src/syntax/error_reporter.gleam`):
- ✅ 3 lines of context before/after errors
- ✅ Type information displayed in error messages
- ✅ Educational notes explaining WHY errors occur
- ✅ 3 actionable hints per error type
- ✅ Better type pretty-printing

**Golden Files**:
- ✅ All examples have `.output.txt` files
- ✅ Error messages include emojis and formatting
- ✅ Source snippets with line numbers
- ✅ Notes and hints included

**Documentation**:
- ✅ `examples/README.md` - Guidelines for adding examples
- ✅ `docs/plans/testing/01-overview.md` - Testing overview
- ✅ `docs/plans/testing/03-examples-testing.md` - Examples testing spec
- ✅ `docs/plans/testing/04-cli-golden-files.md` - Golden file format
- ✅ `docs/plans/testing/05-error-message-improvements.md` - Error improvements (complete)

### ⏳ In Progress

**Tao Language Testing**:
- [ ] Tao example structure
- [ ] Tao-specific golden files
- [ ] Integration with core examples

### 📋 Planned

**Enhanced Testing**:
- [ ] Round-trip tests (parse → format → parse)
- [ ] Performance benchmarks
- [ ] Regression test suite for bug fixes

**Future Error Improvements**:
- [ ] "Did you mean?" suggestions (blocked by De Bruijn indices)
- [ ] Full type pretty-printing for dependent types
- [ ] Error chaining for cascading errors

---

## Key Concepts

### Golden File Format

**Success Example** (`programs/add.output.txt`):
```
3
```

**Error Example** (`errors/type_errors/type_mismatch.output.txt`):
```
❌ error[E0101]: Type mismatch
   ┌─ examples/core/errors/type_errors/type_mismatch.core.tao:2:5
   │
 1 │ // This type annotation doesn't match the value's type.
 2 │ 1 : $Type
   │     ^~~~~ value is Int, but it should be $Type
   │
   💡 The value 1 is of type Int
   💡 The type annotation expects a value of type $Type
   📝 note: Int and $Type are incompatible types
   🔧 help: Did you mean? `1 : Int`
-----------------------------------------------------------
1
```

### Test Categories

| Category | Directory | Expectation | Golden File |
|----------|-----------|-------------|-------------|
| Programs | `programs/` | Success | Normalized term |
| Terms | `terms/` | Success | Normalized term |
| Type Errors | `errors/type_errors/` | Error | Full error output |
| Syntax Errors | `errors/syntax_errors/` | Error | Full error output |
| Syntax Recovery | `errors/syntax_recovery/` | Error | Full error output |
| Exhaustiveness | `errors/exhaustiveness_checks/` | Error | Full error output |

---

## Example Usage

### Adding a New Example

1. **Create the source file**:
   ```gleam
   // examples/core/programs/16_function_composition.core.tao
   // Function Composition
   // Demonstrates composing two functions: (f ∘ g)(x) = f(g(x))
   let compose = f -> g -> x -> f(g(x)) in
   let double = x -> x * 2 in
   let increment = x -> x + 1 in
   compose(double)(increment)(5)
   ```

2. **Generate golden file**:
   ```bash
   gleam run run examples/core/programs/16_function_composition.core.tao > examples/core/programs/16_function_composition.output.txt
   ```

3. **Run tests**:
   ```bash
   gleam test
   ```

### Updating Golden Files

When CLI output changes intentionally:

```bash
# Regenerate all golden files
./scripts/generate_golden_files.sh

# Review changes
git diff examples/core/

# Run tests to verify
gleam test
```

---

## Related Documents

- **[02-e2e-test-enhancement.md](./02-e2e-test-enhancement.md)** - E2E test implementation (complete)
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing specification
- **[../cli/01-overview.md](../cli/01-overview.md)** - CLI overview
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - Check/Run commands spec
- **[../../examples/README.md](../../examples/README.md)** - Examples guide

---

## References

- [E2E Test Implementation](../../test/core/examples_test.gleam)
- [Examples Directory](../../examples/core/)
- [Golden File Script](../../scripts/generate_golden_files.sh)
