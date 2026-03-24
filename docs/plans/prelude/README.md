# Prelude Implementation Plan

> **Goal**: Create a minimal prelude to dogfood the Tao compiler implementation
> **Status**: 📋 **Planned** - Not started
> **Date**: March 2026
> **Priority**: High - Required for self-hosting effort

---

## Executive Summary

**Purpose**: The prelude is the foundation of the Tao standard library. It provides essential types (`Bool`, `Option`, `Result`) that are auto-imported in every Tao program.

**Why start here?**: Writing the prelude will:
1. **Dogfood the compiler** - Test Tao's type system, pattern matching, and error messages
2. **Identify gaps** - Discover what's missing for practical programming
3. **Build incrementally** - Each module is self-contained and testable
4. **Create reusable components** - All Tao programs will use these types

**Estimated effort**: 1-2 weeks for initial implementation

---

## Motivation: Why the Prelude First?

From **[SELF-HOSTING-ANALYSIS.md](../SELF-HOSTING-ANALYSIS.md)**:

> **What you need to write a compiler**:
> ```tao
> // Can't do this yet:
> import list.{map, filter, fold}
> import string.{join, split, length}
> import option.{Option, Some, None}
> import result.{Result, Ok, Err}
> ```

The prelude provides the **minimum viable standard library** needed to write real programs. Without it, you can't:
- Handle errors properly (no `Result`)
- Represent optional values (no `Option`)
- Write boolean logic (no `Bool`)

---

## Module Structure

### File Organization

```
lib/prelude/
├── bool.tao       # Boolean type and operations
├── option.tao     # Option type and operations
└── result.tao     # Result type and operations

examples/prelude/
├── 01_bool_examples.tao
├── 02_option_examples.tao
└── 03_result_examples.tao

test/prelude/
├── bool_test.tao
├── option_test.tao
└── result_test.tao
```

### Import System

**Directory-based imports**: Importing `prelude` automatically imports all public modules (files not starting with `_`):

```tao
// Import all public prelude modules
import prelude

// Now these are available:
let x: Bool = True
let y: Option(I32) = Some(42)
let z: Result(I32, String) = Ok(42)

// Private modules (starting with _) are not exported:
// lib/prelude/_internal.tao  -- internal implementation, not exported
```

**Note**: Files use `.tao` extension (Tao language syntax).

---

## Implementation Phases

### Phase 1: Bool (2-3 days) - **START HERE**

**Goal**: Boolean type with logical operations.

```tao
// lib/prelude/bool.tao

// Type definition
type Bool = True | False

// Logical operations
fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}
```

**Deliverables**:
- [ ] `lib/prelude/bool.tao` with type and operations
- [ ] Examples and tests (REPL-style in same file)
- [ ] Verify error messages work for type errors
- [ ] Document issues in **[01-bool.md](./01-bool.md)**

**See**: **[01-bool.md](./01-bool.md)** for detailed Bool implementation plan

---

### Phase 2: Numbers (3-4 days)

**Goal**: Numeric types with arithmetic and comparison operators.

```tao
// lib/prelude/numbers.tao

// Type aliases (backed by Core FFI)
type I32 = %prim_i32
type I64 = %prim_i64
type F32 = %prim_f32
type F64 = %prim_f64

// Arithmetic operators (overloaded)
fn (+)(a: I32, b: I32) -> I32 { %call i32_add(a, b) }
fn (+)(a: I64, b: I64) -> I64 { %call i64_add(a, b) }
// ... etc for -, *, /, %

// Comparison operators (return Bool)
fn (==)(a: I32, b: I32) -> Bool { %call i32_eq(a, b) }
fn (<)(a: I32, b: I32) -> Bool { %call i32_lt(a, b) }
// ... etc for !=, <=, >, >=
```

**Key focus**: Test operator overloading mechanism.

**Deliverables**:
- [ ] `lib/prelude/numbers.tao` with types and operators
- [ ] Examples and tests (REPL-style in same file)
- [ ] Verify operator overloading resolves correctly
- [ ] Document issues in **[02-numbers.md](./02-numbers.md)**

**See**: **[02-numbers.md](./02-numbers.md)** for detailed Numbers implementation plan

---

### Phase 3: Option (3-4 days)

**Goal**: Optional value type with safe extraction.

```tao
// lib/prelude/option.tao

// Type definition
type Option(a) = Some(a) | None

// Predicates
fn is_some(opt: Option(a)) -> Bool {
  match opt {
    | Some(_) -> True
    | None -> False
  }
}

fn is_none(opt: Option(a)) -> Bool {
  match opt {
    | Some(_) -> False
    | None -> True
  }
}

// Extraction
fn unwrap(opt: Option(a)) -> a {
  match opt {
    | Some(x) -> x
    | None -> panic("unwrap called on None")
  }
}

fn unwrap_or(opt: Option(a), default: a) -> a {
  match opt {
    | Some(x) -> x
    | None -> default
  }
}

// Functor operations
fn map(opt: Option(a), f: (a) -> b) -> Option(b) {
  match opt {
    | Some(x) -> Some(f(x))
    | None -> None
  }
}

fn and_then(opt: Option(a), f: (a) -> Option(b)) -> Option(b) {
  match opt {
    | Some(x) -> f(x)
    | None -> None
  }
}
```

**Deliverables**:
- [ ] `lib/prelude/option.tao` with type and operations
- [ ] `examples/prelude/02_option_examples.tao` with usage examples
- [ ] `test/prelude/option_test.tao` with golden file tests
- [ ] Test polymorphic type instantiation
- [ ] Document issues in `02-option.md`

---

### Phase 3: Result (3-4 days)

**Goal**: Error handling type with error propagation.

```tao
// lib/prelude/result.tao

// Type definition
type Result(a, e) = Ok(a) | Err(e)

// Predicates
fn is_ok(result: Result(a, e)) -> Bool {
  match result {
    | Ok(_) -> True
    | Err(_) -> False
  }
}

fn is_err(result: Result(a, e)) -> Bool {
  match result {
    | Ok(_) -> False
    | Err(_) -> True
  }
}

// Extraction
fn unwrap(result: Result(a, e)) -> a {
  match result {
    | Ok(x) -> x
    | Err(e) -> panic("unwrap called on Err: " <> to_string(e))
  }
}

fn unwrap_or(result: Result(a, e), default: a) -> a {
  match result {
    | Ok(x) -> x
    | Err(_) -> default
  }
}

// Functor operations
fn map(result: Result(a, e), f: (a) -> b) -> Result(b, e) {
  match result {
    | Ok(x) -> Ok(f(x))
    | Err(e) -> Err(e)
  }
}

fn map_err(result: Result(a, e), f: (e) -> f) -> Result(a, f) {
  match result {
    | Ok(x) -> Ok(x)
    | Err(e) -> Err(f(e))
  }
}

fn and_then(result: Result(a, e), f: (a) -> Result(b, e)) -> Result(b, e) {
  match result {
    | Ok(x) -> f(x)
    | Err(e) -> Err(e)
  }
}
```

**Deliverables**:
- [ ] `lib/prelude/result.tao` with type and operations
- [ ] `examples/prelude/03_result_examples.tao` with usage examples
- [ ] `test/prelude/result_test.tao` with golden file tests
- [ ] Test error propagation patterns
- [ ] Document issues in `03-result.md`

---

## Out of Scope (For Now)

### Ordering Type

**Decision**: Skip dedicated `Ordering` type. Comparison operations work through operator overloading:

```tao
// Use operators directly
fn max(a: I32, b: I32) -> I32 {
  if a > b { a } else { b }
}

fn compare(a: I32, b: I32) -> I32 {
  if a == b { 0 }
  else if a < b { -1 }
  else { 1 }
}
```

This is simpler and more pragmatic than a separate `Ordering` type.

---

## Dogfooding Process

### Weekly Cycle

**Week 1**: Write Bool module
- Day 1-2: Write type definition
- Day 3-4: Write logical operations
- Day 5: Write examples and tests

**Week 2**: Write Option module
- Day 1-2: Write type definition
- Day 3-4: Write predicates and extraction
- Day 5: Write functor operations

**Week 3**: Write Result module
- Day 1-2: Write type definition
- Day 3-4: Write error handling operations
- Day 5: Integration testing

### Issue Tracking

During implementation, track issues in module-specific plan files:

| Module | Issue Tracker |
|--------|---------------|
| Bool | **[01-bool.md](./01-bool.md)** |
| Option | `02-option.md` (to be created) |
| Result | `03-result.md` (to be created) |

### Issue Template

```markdown
## Issue #NN: [Brief description]

**Category**: Type system / Pattern matching / Error messages / Syntax / Other

**Code**:
```tao
// Minimal reproducing example
fn example() {
  // ... code that fails or is awkward
}
```

**Expected**: What should happen

**Actual**: What actually happens

**Error message**:
```
Full error message from compiler
```

**Severity**:
- 🔴 **Blocker** - Cannot proceed without fix
- 🟡 **Pain point** - Can work around, but awkward
- 🟢 **Nice to have** - Would improve UX

**Workaround**: If any

**Fix**: If known
```

---

## Known Challenges

### Wildcard Pattern Exhaustiveness 🔴

**Issue**: Wildcard patterns (`_`) may not be recognized as exhaustive.

**Workaround**: Use variable patterns instead:
```tao
match opt {
  | Some(x) -> x
  | n -> default  // Use variable instead of _
}
```

**Fix**: See **[../core/18-exhaustiveness-wildcard-bug.md](../core/18-exhaustiveness-wildcard-bug.md)**

---

### Polymorphic Constructor Instantiation 🟡

**Issue**: `Option(a)` requires type parameter instantiation.

**Workaround**: Use explicit type annotations:
```tao
let x: Option(I32) = Some(42)
```

---

### String Concatenation in Error Messages 🟡

**Issue**: `panic("unwrap called on None")` requires string type.

**Workaround**: Use simple error messages or defer panic implementation.

---

## Success Criteria

The prelude is complete when:

1. ✅ All three modules compile without errors
2. ✅ All operations type-check correctly
3. ✅ Example programs run successfully
4. ✅ Golden file tests pass
5. ✅ Error messages are clear and actionable
6. ✅ Can write simple programs using only prelude types

---

## Testing

### Test Infrastructure

**Critical**: Before implementing prelude modules, the testing infrastructure must be in place.

**See**: **[../tao/18-stdlib-testing.md](../tao/18-stdlib-testing.md)** for testing infrastructure implementation plan.

The testing infrastructure provides:
1. **Internal API** - `run_test_file()` returns `#(List(Error), List(TestResult))`
2. **Syntax checking** - Verifies no parse errors
3. **Type checking** - Verifies no type errors
4. **Exhaustiveness checking** - Verifies pattern matches are exhaustive
5. **Evaluation** - Verifies expressions produce expected results
6. **Simple return** - Just data, no formatting

### Separation of Concerns

| Component | Responsibility |
|-----------|----------------|
| **test_api.gleam** | Returns `#(errors, results)` - no formatting |
| **CLI** | Pretty-prints errors and results |
| **Gleam tests** | Check `errors == []` and `results != []` |

### Test Directory Structure

```
test/lib/prelude/
├── bool_test.tao       # Tests for Bool module
├── numbers_test.tao    # Tests for Numbers module
├── option_test.tao     # Tests for Option module
└── result_test.tao     # Tests for Result module
```

### Test File Format

Tests use REPL-style format in the same file as examples:

```tao
// lib/prelude/bool.tao

import prelude

// Examples with expected results (doubles as tests)
> not(True)
False

> not(False)
True

> and(True, True)
True

> and(True, False)
False
```

### Running Tests

```bash
# Run all stdlib tests
gleam test

# Run specific stdlib test file via CLI
gleam run test test/lib/prelude/bool_test.tao
```

### Gleam Test Usage

```gleam
// test/tao/stdlib_prelude_test.gleam

import tao/test_api
import gleeunit
import gleeunit/should

pub fn prelude_bool_no_errors_test() {
  let source = read_file("lib/prelude/bool.tao")
  let #(errors, _results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  errors |> should.equal([])
}

pub fn prelude_bool_tests_run_test() {
  let source = read_file("lib/prelude/bool.tao")
  let #(_errors, results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  results |> should.not.equal([])
}
```

**Key points**:
- Check `errors == []` - no syntax/type/exhaustiveness errors
- Check `results != []` - at least one test ran
- Don't check exact test count - avoids updating tests when adding new examples

### Test Coverage

Each module should have tests for:
1. **Happy path** - Normal successful usage
2. **Edge cases** - Boundary conditions
3. **Error cases** - Functions that panic or return errors
4. **Polymorphism** - Different type instantiations (for generic functions)

### Shared Helpers

Both CLI and tests share:
- **Parsing** - `tao_parse()`
- **Type checking** - `tao_type_check()`
- **Evaluation** - `evaluate()`

The CLI adds pretty-printing on top of the raw data from test API.

---

## Related Documents

- **[01-bool.md](./01-bool.md)** - Bool implementation plan (START HERE)
- **[02-numbers.md](./02-numbers.md)** - Numbers implementation plan
- **[../tao/18-stdlib-testing.md](../tao/18-stdlib-testing.md)** - Testing infrastructure (MUST BE DONE FIRST)
- **[../stdlib/01-overview.md](../stdlib/01-overview.md)** - Standard library overview
- **[../stdlib/02-prelude.md](../stdlib/02-prelude.md)** - Existing prelude specification
- **[../SELF-HOSTING-ANALYSIS.md](../SELF-HOSTING-ANALYSIS.md)** - Self-hosting roadmap
- **[../tao/03-syntax.md](../tao/03-syntax.md)** - Tao syntax specification

---

## Implementation Order

**CRITICAL**: Testing infrastructure must be implemented before prelude modules.

1. **[../tao/18-stdlib-testing.md](../tao/18-stdlib-testing.md)** - Testing infrastructure (PREREQUISITE)
2. **[01-bool.md](./01-bool.md)** - Bool module (first prelude module)
3. **[02-numbers.md](./02-numbers.md)** - Numbers module (tests operator overloading)
4. Option module - After Bool and Numbers are working
5. Result module - After Option is working

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial plan created - Restructured to module-specific plans |
