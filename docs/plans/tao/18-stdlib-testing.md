# Standard Library Testing Infrastructure

> **Goal**: Create testing infrastructure for standard library modules
> **Status**: 📋 **Planned** - Not started
> **Date**: March 2026
> **Priority**: **CRITICAL** - Must be implemented before prelude work begins

---

## Overview

**Problem**: We need to test standard library modules (`lib/prelude/*.tao`) to ensure:
1. No syntax errors
2. No type errors
3. No exhaustiveness checking errors
4. All expressions evaluate to expected results

**Current state**: CLI `test` command spawns subprocess, not suitable for library testing.

**Goal**: Simple internal API that returns errors and results. CLI and tests use the same API but handle output differently.

---

## Requirements

### Functional Requirements

1. **Parse checking** - Verify no syntax errors in source files
2. **Type checking** - Verify no type errors after desugaring
3. **Exhaustiveness checking** - Verify pattern matches are exhaustive
4. **Evaluation** - Verify expressions produce expected results
5. **Return tuple** - `#(List(Error), List(TestResult))`

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
├── test_api.gleam         # NEW: Internal testing API
└── compiler_bootstrap.gleam # CLI: Pretty-prints results

test/lib/
└── prelude/
    ├── bool_test.tao
    ├── numbers_test.tao
    └── ...
```

### API Design

```gleam
// src/tao/test_api.gleam

/// Test result for a single expression
pub type TestResult {
  Pass(expression: String)
  Fail(expression: String, expected: String, actual: String)
}

/// Run all tests in a file
/// Returns: #(errors, test_results)
/// - errors: Parse/type/exhaustiveness errors
/// - test_results: List of pass/fail for each test expression
pub fn run_test_file(source: String, file_path: String) -> #(List(Error), List(TestResult)) {
  // 1. Parse
  let parse_result = tao_parse(source)
  case parse_result {
    Error(e) -> #([ParseError(e, span)], [])
    Ok(ast) -> {
      // 2. Type check
      let type_result = tao_type_check(ast)
      case type_result {
        Error(e) -> #([TypeError(e, span)], [])
        Ok(checked_ast) -> {
          // 3. Extract test expressions (> expr\nexpected format)
          let tests = extract_tests(checked_ast)
          
          // 4. Run each test
          let results = list.map(tests, fn(test) {
            run_single_test(test, checked_ast)
          })
          
          #([], results)
        }
      }
    }
  }
}

/// Run a single test expression
fn run_single_test(test: TestExpr, ast: CheckedAST) -> TestResult {
  // Evaluate expression
  let actual = evaluate(test.expression, ast)
  
  // Evaluate expected
  let expected = evaluate(test.expected, ast)
  
  // Compare (internal comparison, not exposed)
  if values_equal(actual, expected) {
    Pass(test.expression)
  } else {
    Fail(test.expression, test.expected, format(actual))
  }
}

/// Internal value equality (not exposed to users)
fn values_equal(a: Value, b: Value) -> Bool {
  // Simple structural comparison
  // No pretty-printing, no formatting
}

/// Internal format for Fail results (minimal)
fn format(value: Value) -> String {
  // Minimal string representation
}
```

---

## Test File Format

### REPL-Style Tests

```tao
// test/lib/prelude/bool_test.tao

import prelude

// Test format: > expression\nexpected_result

> not(True)
False

> not(False)
True

> and(True, True)
True

> and(True, False)
False

> or(True, False)
True

> or(False, False)
False
```

### Test Extraction

Tests are extracted from source files by parsing lines matching:
```
> <expression>
<expected_result>
```

The test runner:
1. Parses the file as Tao source
2. Extracts test expressions from comments/annotations
3. Evaluates each expression
4. Compares result with expected value
5. Returns `#(errors, results)`

---

## Implementation Plan

### Phase 1: Core Testing API (2-3 days)

**Goal**: Internal API that returns `#(List(Error), List(TestResult))`.

#### Step 1.1: Create Test API Module

```gleam
// src/tao/test_api.gleam

import tao/syntax
import tao/desugar
import tao/global_context
import core/core
import core/syntax

pub type Error {
  ParseError(message: String, span: Span)
  TypeError(message: String, span: Span)
  ExhaustivenessError(message: String, span: Span)
  EvaluationError(message: String, span: Span)
}

pub type TestResult {
  Pass(expression: String)
  Fail(expression: String, expected: String, actual: String)
}

/// Parse, type-check, and evaluate a test file
/// Returns: #(errors, test_results)
pub fn run_test_file(source: String, file_path: String) -> #(List(Error), List(TestResult)) {
  // 1. Parse Tao source
  let ast = case tao_parse(source) {
    Ok(ast) -> ast
    Error(e) -> return #([ParseError(e, span)], [])
  }
  
  // 2. Desugar to Core
  let core_term = case desugar_module(ast) {
    Ok(term) -> term
    Error(e) -> return #([DesugarError(e)], [])
  }
  
  // 3. Type check
  let state = initial_state()
  let #(_value, _type, state) = infer(state, core_term)
  
  case state.errors {
    [] -> Nil  // OK, continue
    errors -> return #(errors, [])
  }
  
  // 4. Extract and run tests
  let tests = extract_repl_tests(source)
  let results = list.map(tests, fn(test) {
    run_test(test, state)
  })
  
  #([], results)
}

/// Extract REPL-style tests from source
fn extract_repl_tests(source: String) -> List(TestExpr) {
  // Parse lines matching "> expr\nexpected"
  // Return list of {expression, expected} pairs
}

/// Run a single test
fn run_test(test: TestExpr, state: State) -> TestResult {
  // Evaluate expression
  let actual_value = evaluate(state, test.expression)
  
  // Parse and evaluate expected
  let expected_value = evaluate(state, test.expected)
  
  // Compare (internal)
  if values_equal(actual_value, expected_value) {
    Pass(test.expression)
  } else {
    Fail(test.expression, test.expected, minimal_format(actual_value))
  }
}

/// Internal value equality
fn values_equal(a: Value, b: Value) -> Bool {
  // Direct structural comparison
  // No pretty-printing involved
}

/// Minimal format for Fail results
fn minimal_format(value: Value) -> String {
  // Simple string representation
}
```

---

### Phase 2: CLI Integration (1-2 days)

**Goal**: CLI pretty-prints the results from test API.

#### Step 2.1: Update CLI Test Command

```gleam
// src/compiler_bootstrap.gleam

import tao/test_api

pub fn run_test_command(paths: List(String), ...) {
  // For each test file
  list.flat_map(paths, fn(path) {
    let source = read_file(path)
    let #(errors, results) = test_api.run_test_file(source, path)
    
    // CLI pretty-prints errors
    case errors {
      [] -> Nil
      _ -> print_errors(errors)
    }
    
    // CLI pretty-prints test results
    print_test_results(results)
  })
}

/// Pretty-print test results (CLI only)
fn print_test_results(results: List(TestResult)) {
  let passed = list.filter(results, is_pass) |> list.length
  let failed = list.filter(results, is_fail) |> list.length
  
  io.println("Passed: " <> int.to_string(passed))
  io.println("Failed: " <> int.to_string(failed))
  
  // Print failures with details
  list.filter(results, is_fail)
  |> list.each(fn(f) { print_failure(f) })
}
```

#### Step 2.2: Update CLI Run Command

```gleam
// src/compiler_bootstrap.gleam

pub fn run_run_command(file: String, ...) {
  let source = read_file(file)
  
  // Parse, type-check, evaluate
  case compile_and_run(source) {
    Ok(value) -> io.println(pretty_print(value))
    Error(e) -> print_error(e)
  }
}

/// Pretty-print for CLI (not used by tests)
fn pretty_print(value: Value) -> String {
  // Full pretty-printing with formatting
}
```

---

### Phase 3: Test Directory Structure (1 day)

**Goal**: Organize test files for stdlib modules.

```
test/lib/
└── prelude/
    ├── bool_test.tao
    ├── numbers_test.tao
    ├── option_test.tao
    └── result_test.tao
```

#### Example Test File

```tao
// test/lib/prelude/bool_test.tao

import prelude

// not tests
> not(True)
False

> not(False)
True

// and tests
> and(True, True)
True

> and(True, False)
False

> and(False, True)
False

> and(False, False)
False

// or tests
> or(True, True)
True

> or(True, False)
True

> or(False, True)
True

> or(False, False)
False
```

---

## Usage Examples

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

pub fn prelude_bool_all_pass_test() {
  let source = read_file("lib/prelude/bool.tao")
  let #(errors, results) = test_api.run_test_file(source, "lib/prelude/bool.tao")
  
  errors |> should.equal([])
  results |> should.not.equal([])
  
  // All tests should pass
  let failures = list.filter(results, fn(r) { is_fail(r) })
  failures |> should.equal([])
}
```

### CLI Usage

```bash
# Run stdlib tests via CLI
gleam run test test/lib/prelude/bool_test.tao

# Output (pretty-printed by CLI):
# Passed: 12
# Failed: 0
```

---

## Testing the Testing Infrastructure

### Self-Test

The testing infrastructure should be tested itself:

```gleam
// test/tao/test_api_test.gleam

import tao/test_api
import gleeunit
import gleeunit/should

pub fn run_test_file_returns_no_errors_test() {
  let source = "
    import prelude
    
    > not(True)
    False
    
    > not(False)
    True
  "
  
  let #(errors, results) = test_api.run_test_file(source, "test.tao")
  errors |> should.equal([])
  results |> should.not.equal([])
}

pub fn run_test_file_returns_errors_for_type_error_test() {
  let source = "
    import prelude
    
    > not(42)  // Type error
    False
  "
  
  let #(errors, _results) = test_api.run_test_file(source, "test.tao")
  errors |> should.not.equal([])
}

pub fn run_test_file_detects_failures_test() {
  let source = "
    import prelude
    
    > not(True)
    True  // Wrong expected value
  "
  
  let #(_errors, results) = test_api.run_test_file(source, "test.tao")
  let failures = list.filter(results, fn(r) { is_fail(r) })
  failures |> should.not.equal([])
}
```

---

## Integration with Existing Tests

### Current Test Structure

```
test/
├── tao/
│   ├── syntax_test.gleam      // Gleam tests for Tao parser
│   └── desugarer_test.gleam   // Gleam tests for desugarer
└── ...
```

### New Test Structure

```
test/
├── tao/
│   ├── syntax_test.gleam      // Gleam tests for Tao parser
│   ├── desugarer_test.gleam   // Gleam tests for desugarer
│   └── test_api_test.gleam    // Gleam tests for test API
└── lib/
    └── prelude/
        ├── bool_test.tao      // Tao tests for Bool module
        └── numbers_test.tao   // Tao tests for Numbers module
```

### Running All Tests

```bash
# Run Gleam tests (parser, desugarer, test API, stdlib wrappers)
gleam test

# Run Tao library tests via CLI
gleam run test test/lib/prelude/bool_test.tao
```

---

## Separation of Concerns

| Component | Responsibility |
|-----------|----------------|
| **test_api.gleam** | Parse, type-check, evaluate, compare. Return `#(errors, results)` |
| **compiler_bootstrap.gleam** | Pretty-print errors and results for CLI |
| **Gleam tests** | Check `errors == []` and `results != []` |

### What test_api Does NOT Do

- ❌ No pretty-printing
- ❌ No formatting for display
- ❌ No structural equality exposure
- ❌ No CLI output

### What CLI Does

- ✅ Pretty-prints errors with source snippets
- ✅ Pretty-prints test results (passed/failed counts)
- ✅ Shows failure details (expected vs actual)

### What Gleam Tests Do

- ✅ Check `errors == []`
- ✅ Check `results != []`
- ✅ Optionally check all tests pass

---

## Success Criteria

The testing infrastructure is complete when:

1. ✅ `test_api.run_test_file()` returns `#(List(Error), List(TestResult))`
2. ✅ No pretty-printing in test_api
3. ✅ CLI pretty-prints results
4. ✅ Gleam tests check `errors == []` and `results != []`
5. ✅ Test files in `test/lib/prelude/` work correctly
6. ✅ All existing Gleam tests still pass
7. ✅ Clear separation: test_api returns data, CLI formats

---

## Implementation Checklist

### Phase 1: Core Testing API

- [ ] Create `src/tao/test_api.gleam`
- [ ] Define `Error` type
- [ ] Define `TestResult` type (Pass/Fail)
- [ ] Implement `run_test_file()` returning `#(errors, results)`
- [ ] Implement test extraction from REPL-style format
- [ ] Implement internal value comparison (not exposed)

### Phase 2: CLI Integration

- [ ] Update `src/compiler_bootstrap.gleam` test command
- [ ] Add pretty-printing for errors (CLI only)
- [ ] Add pretty-printing for test results (CLI only)
- [ ] Test with existing Tao examples

### Phase 3: Test Directory Structure

- [ ] Create `test/lib/prelude/` directory
- [ ] Create `bool_test.tao` example
- [ ] Create Gleam wrapper test: `test/tao/stdlib_prelude_test.gleam`
- [ ] Verify test discovery and execution

### Phase 4: Self-Testing

- [ ] Create `test/tao/test_api_test.gleam`
- [ ] Test successful execution (no errors, some results)
- [ ] Test error detection (parse, type, exhaustiveness)
- [ ] Test failure detection (wrong expected values)

---

## Related Documents

- **[../testing/01-overview.md](../testing/01-overview.md)** - Testing overview
- **[../testing/04-cli-golden-files.md](../testing/04-cli-golden-files.md)** - CLI golden file tests
- **[01-bool.md](../prelude/01-bool.md)** - Bool implementation (first user of test API)
- **[../core/core.gleam](../../src/core/core.gleam)** - Core evaluation

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial testing infrastructure plan created |
