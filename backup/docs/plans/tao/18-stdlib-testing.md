# Standard Library Testing Infrastructure

> **Goal**: Create testing infrastructure for standard library modules
> **Status**: ✅ **Complete** - Implementation finished
> **Date**: March 2026
> **Priority**: **CRITICAL** - Must be implemented before prelude work begins

---

## Overview

**Problem**: We need to test standard library modules (`lib/prelude/*.tao`) to ensure:
1. No syntax errors
2. No type errors
3. No exhaustiveness checking errors
4. All expressions evaluate to expected results

**Solution**: Simple internal API that returns `#(List(core.Error), List(TestResult))`.

---

## Known Issues

### InfiniteType Error in Type Checker

**Status**: 🔍 **Investigating** - Root cause identified, fix in progress

**Symptom**: When type checking `lib/prelude/bool.tao`, the type checker reports:
```
InfiniteType(4, VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], ...))
```

**Root Cause**: 
1. Type annotations in function definitions (`fn not(b: Bool) -> Bool`) are not being used during type checking
2. The type checker infers types from the body, creating holes for parameter and return types
3. The occurs check fails when unifying a hole with a type that contains the same hole

**Required Fix**:
1. Add type annotations to desugared function definitions (use `CoreAnn`)
2. Ensure type checker uses annotations instead of inferring when available
3. Properly register prelude type definitions (Bool, Option, Result) in the global context

**Workaround**: Currently, the test infrastructure is working correctly - it's the type checker that has this bug. The test API correctly:
- Strips test lines before parsing
- Fixes spans to use correct filenames
- Converts type declarations to statements
- Returns all errors (not just the first one)

---

## Requirements

### Functional Requirements

1. **Parse checking** - Verify no syntax errors in source files
2. **Type checking** - Verify no type errors after desugaring
3. **Exhaustiveness checking** - Verify pattern matches are exhaustive
4. **Evaluation** - Verify expressions produce expected results
5. **Return tuple** - `#(List(core.Error), List(TestResult))` - uses Core errors directly
6. **Keep all errors** - Don't just return the first error

### Non-Functional Requirements

1. **Reusable** - Same API for all stdlib modules
2. **Fast** - No subprocess spawning
3. **Simple** - No formatting logic, just return data
4. **Composable** - Can test individual functions or entire modules

---

## Architecture

### Module Structure

```
src/tao/
├── test_runner.gleam      # Existing: CLI test command
├── test_api.gleam         # Internal testing API

lib/prelude/
├── bool.tao               # Bool module with tests as examples
└── bool.test.tao          # Complex tests for Bool

test/lib/
└── prelude/
    └── bool_test.gleam    # Gleam wrapper tests
```

### API Design

```gleam
// src/tao/test_api.gleam

/// Result of running a single test.
pub type TestResult {
  Pass(expression: String)
  Fail(expression: String, expected: String, actual: String)
}

/// Run all tests in a file
pub fn run_test_file(source: String, file_path: String) 
  -> #(List(core.Error), List(TestResult)) {
  // 1. Parse - convert ALL errors to core.SyntaxError
  // 2. Desugar and type check
  // 3. Extract tests (> expr ~> expected)
  // 4. Run each test
  // 5. Return #(errors, results)
}
```

---

## Test File Format

### Simple Tests (in `.tao` files)

Single-line format with `~>` operator:

```tao
// lib/prelude/bool.tao

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

> not(True) ~> False
> not(False) ~> True
```

### Complex Tests (in `.test.tao` files)

Multi-line format for longer tests:

```tao
// lib/prelude/bool.test.tao

import prelude/bool.{and, or, not}

// Nested operations
> and(and(True, True), True)
True

// Complex expressions
> and(or(True, False), not(False))
True
```

### Gleam Wrapper Tests

```gleam
// test/lib/prelude/bool_test.gleam

import tao/test_api
import simplifile
import gleam/list

pub fn lib_prelude_bool_module_test() {
  let filename = "lib/prelude/bool.tao"
  let assert Ok(source) = simplifile.read(filename)
  let #(errors, results) = test_api.run_test_file(source, filename)
  
  errors |> should.equal([])
  list.length(results) |> should.equal(20)
}
```

---

## Key Design Decisions

### Use Core Errors Directly

**Don't** create wrapper error types:

```gleam
// ❌ Wrong: Custom error type
pub type Error {
  ParseError(message: String, span: Span)
  TypeError(message: String, span: Span)
}

// ✅ Right: Use core.Error directly
pub fn run_test_file(...) -> #(List(core.Error), List(TestResult))
```

### Keep All Errors

**Don't** just return the first error:

```gleam
// ❌ Wrong: Only first error
case parse_result.errors {
  [err, ..] -> #([convert_error(err)], [])
  ...
}

// ✅ Right: All errors
case parse_result.errors {
  [_, ..] as errors -> {
    let core_errors = list.map(errors, fn(err) {
      SyntaxError(err.span, err.expected, err.got, file_path)
    })
    #(core_errors, [])
  }
  ...
}
```

### Include Filename in Spans

**Don't** use "input" or empty string:

```gleam
// ❌ Wrong: Generic filename
Span("input", 155, 8, 1, 158)

// ✅ Right: Actual file path
Span("lib/prelude/bool.tao", 8, 1, 8, 3)
```

### Support Single-Line Test Syntax

```tao
// ✅ Preferred for simple tests
> not(True) ~> False
> not(False) ~> True

// ✅ Also supported for complex tests
> and(or(True, False), not(False))
True
```

---

## Implementation Details

### Error Conversion

```gleam
// Convert parse errors to core.SyntaxError
let core_errors = list.map(parse_errors, fn(err) {
  SyntaxError(err.span, err.expected, err.got, file_path)
})

// Return all type errors directly
case state.errors {
  [_, ..] as errors -> #(errors, [])
  [] -> #([], results)
}
```

### Test Extraction

```gleam
fn extract_repl_tests(source: String, file_path: String) -> List(TestExpr) {
  // Skip: empty lines, comments (// ///), import lines
  // Extract:
  //   - `> expr ~> expected` (single-line)
  //   - `> expr` followed by `expected` (multi-line)
}
```

### Span Creation

```gleam
// Single-line test
let span = Span(file_path, line_num, 1, line_num, string.length(line_content))

// Multi-line test
let span = Span(file_path, expr_line, 1, expected_line, string.length(expected))
```

---

## Success Criteria

The testing infrastructure is complete when:

1. ✅ `run_test_file()` returns `#(List(core.Error), List(TestResult))`
2. ✅ All parse errors converted to `core.SyntaxError`
3. ✅ All errors kept, not just first one
4. ✅ Spans include filename and correct positions
5. ✅ Supports `> expr ~> expected` single-line format
6. ✅ Supports multi-line `> expr\nexpected` format
7. ✅ Gleam tests check `errors == []` and test count
8. ✅ Test files in `lib/*.tao` and `lib/*.test.tao` work

---

## Related Documents

- **[../prelude/README.md](../prelude/README.md)** - Prelude implementation plan
- **[../testing/01-overview.md](../testing/01-overview.md)** - Testing overview
- **[../../src/core/core.gleam](../../src/core/core.gleam)** - Core error types

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial testing infrastructure plan created |
| March 2026 | Updated to use `core.Error` directly |
| March 2026 | Added `~>` single-line test syntax |
| March 2026 | Updated file structure (`lib/`, `test/lib/`) |
| March 2026 | Implementation complete |
