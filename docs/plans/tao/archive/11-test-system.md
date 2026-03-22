# Tao Test System

> **Goal**: Implement a test command that runs example-based tests from `.tao` files with selective type-checking
> **Status**: 📋 Planned
> **Date**: March 14, 2026

---

## Status

### What's Working

- ✅ `check` command - type checks Tao files
- ✅ `run` command - runs Tao files (continues on errors)
- ✅ Example syntax in documentation

### What's Pending

- Test syntax parser (multi-line and single-line `~>` format)
- Test filtering and discovery
- Selective type-checking (only check tests that will run)
- Test runner implementation
- `test` CLI command with filtering options
- Test result reporting
- Directory recursion for test discovery

### Related

- See **[10-overloading-design.md](./10-overloading-design.md)** for Tao language features
- See **[../cli/01-overview.md](../cli/01-overview.md)** for CLI architecture

---

## Overview

The Tao test system treats **examples as tests**. Tests are written in a REPL-like syntax that serves dual purposes:

1. **Documentation** - Examples show how to use functions
2. **Verification** - Examples are automatically tested

This approach eliminates the separation between documentation and tests, ensuring examples stay up-to-date.

### Key Innovation: Selective Type-Checking

**Critical Feature**: The `test` command only type-checks tests that will run, not the entire codebase. This enables:

- **Iterative Refactoring** - Run tests for the code you're changing, even if other parts are broken
- **Fast Feedback** - Skip type-checking unrelated code
- **Partial Development** - Test new features without fixing entire codebase

```bash
# Only type-check and run "parse *" tests, even if other code has errors
gleam run test src/ --match "parse *"
```

---

## Test Syntax

### Multi-line Test Format

```tao
-- Integer addition
> 1 + 2
3
```

**Structure**:
1. `-- Test name` (optional, defaults to expression)
2. `> expression` - The code to evaluate
3. `expected_result` - Pattern to match against

### Single-line Test Format

For quick tests, use `~>` shorthand:

```tao
> factorial(0) ~> 1
> factorial(1) ~> 1
> factorial(2) ~> 2
> factorial(3) ~> 6
> factorial(4) ~> 24
> factorial(5) ~> 120
```

### Multi-line Expressions

Support for expressions spanning multiple lines:

```tao
-- Complex expression test
> let x = 1 + 2
> let y = x * 3
> y
9
```

**Parsing rule**: Lines starting with `> ` continue the expression. A line without `> ` ends the expression and starts the expected result.

### Pattern Matching in Expected Results

Expected results are patterns, not just values:

```tao
-- Option type test
> Some(42)
Some(_)

-- Record test
> {a = 1, b = 2}
{a = _, b = _}

-- List test
> [1, 2, 3]
[_, _, _]
```

### Test Annotations (Future)

```tao
-- @skip - Skip this test
> broken_test()
result

-- @timeout 5000 - Custom timeout in ms
> slow_operation()
result

-- @group parser - Group for filtering
> parse_integer()
Success(_)
```

---

## CLI Command: `test`

### Usage

```bash
# Test a single file
gleam run test path/to/file.tao

# Test a directory (recursively finds all .tao files)
gleam run test path/to/tests/

# Test multiple files/directories
gleam run test src/parser.tao src/lexer/ tests/

# Filter tests by name (wildcard support)
gleam run test path/to/tests/ --match "parse *"
gleam run test path/to/tests/ --match "*addition*"
gleam run test path/to/tests/ --match "parse *" --match "eval *"

# List tests without running
gleam run test path/to/tests/ --list

# Verbose output
gleam run test path/to/tests/ --verbose
```

### Options

| Option | Description |
|--------|-------------|
| `<path>...` | One or more files or directories to test |
| `--match <pattern>` | Filter tests by name (wildcard `*` supported, can be repeated) |
| `--list` | List all test names without running |
| `--verbose` | Show detailed output including passed tests |
| `--debug` | Debug mode (print AST, type info) |
| `--no-check` | Skip type-checking entirely (run anyway) |

### Wildcard Pattern Syntax

| Pattern | Matches |
|---------|---------|
| `"exact name"` | Tests with exact name |
| `"*suffix"` | Tests ending with suffix |
| `"prefix*"` | Tests starting with prefix |
| `"*substring*"` | Tests containing substring |
| `"*"` | All tests |

### Behavior

1. **Discover** - Find all `.tao` files in specified paths
2. **Parse** - Parse all files and extract tests
3. **Filter** - Apply `--match` patterns to select tests
4. **List** (optional) - If `--list`, show test names and exit
5. **Type Check** - Only type-check selected tests (not entire codebase)
6. **Run Tests** - Execute selected tests regardless of check errors
7. **Report** - Show test results with filtering info
8. **Exit Code** - Non-zero if:
   - Any type-check errors in selected tests
   - Any tests failed

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All selected tests passed, no check errors in selected tests |
| 1 | Check errors in selected tests or test failures |
| 2 | Runtime error during test execution |
| 3 | File/directory not found |
| 4 | Invalid arguments or patterns |

### Selective Type-Checking

**Key Design Decision**: Only type-check code that is part of selected tests.

```
All tests in file:          Selected tests (--match "parse *"):

┌─────────────────────┐     ┌─────────────────────┐
│ Test: parse int ✓   │     │ Test: parse int ✓   │ ← Type-checked
│ Test: parse expr ✗  │     │ Test: parse expr ✓  │ ← Type-checked
│ Test: eval int ✓    │     │ Test: eval int ✓    │ ← Skipped
│ Test: eval expr ✗   │     │ Test: eval expr ✗   │ ← Skipped
└─────────────────────┘     └─────────────────────┘

Result: Can run "parse *" tests even if "eval *" has errors
```

This enables:
- **Iterative refactoring** - Fix one module at a time
- **Partial development** - Test new code without fixing old code
- **Fast feedback** - Skip unrelated type-checking

### Test Execution Model

Each test is compiled to a match expression:

```gleam
// Test: > 1 + 2 \n 3
match (1 + 2) {
| 3 -> Pass(span, "1 + 2")
| got -> Fail(span, "1 + 2", "3", format(got))
}
```

### Test Result Types

```gleam
pub type TestResult {
  Pass(span: Span, name: String)
  Fail(span: Span, name: String, expected: String, got: String)
  Error(span: Span, name: String, message: String)  // Runtime error
  Skipped(span: Span, name: String, reason: String) // @skip annotation
}
```

---

## Implementation Plan

### Phase 1: Test Syntax Parser

**File**: `src/tao/test_parser.gleam`

```gleam
pub type Test {
  Test(
    name: String,
    expression: Expr,
    expected: Pattern,
    span: Span,
    annotations: List(Annotation),  // @skip, @timeout, @group
  )
}

pub type Annotation {
  Skip(reason: String)
  Timeout(ms: Int)
  Group(name: String)
}

pub fn parse_tests(source: String) -> ParseResult(List(Test)) {
  // Parse multi-line and single-line test formats
}

pub fn extract_test_names(tests: List(Test)) -> List(String) {
  // Get all test names for --list
}
```

**Tasks**:
- [ ] Parse `-- name` comments (test name or annotation)
- [ ] Parse `@skip`, `@timeout`, `@group` annotations
- [ ] Parse `> expression` lines (multi-line support)
- [ ] Parse `~>` single-line tests
- [ ] Parse expected result patterns
- [ ] Handle multi-line expressions (continuation with `> `)
- [ ] Default test name from expression

### Phase 2: Test Filtering

**File**: `src/tao/test_filter.gleam`

```gleam
pub fn matches_pattern(pattern: String, test_name: String) -> Bool {
  // Wildcard matching: "parse *" matches "parse integer"
}

pub fn filter_tests(
  tests: List(Test),
  patterns: List(String),
) -> List(Test) {
  // Filter tests by patterns (OR logic: match any pattern)
}

pub fn list_tests(tests: List(Test)) -> Nil {
  // Print test names for --list
}
```

**Tasks**:
- [ ] Implement wildcard pattern matching (`*` wildcard)
- [ ] Support multiple patterns (OR logic)
- [ ] Case-insensitive matching (optional)
- [ ] List mode (`--list`)

### Phase 3: Selective Type-Checking

**File**: `src/tao/test_type_checker.gleam`

```gleam
pub type CheckResult {
  AllPassed
  HasErrors(List(TypeError))
}

/// Syntax errors are always reported. Type/exhaustiveness errors
/// are only reported for selected tests.
pub fn check_selected_tests(
  tests: List(Test),
  file_source: String,
) -> CheckResult {
  // 1. Parse entire file, report all syntax errors
  // 2. Load all definitions into context as unchecked
  // 3. For each selected test, check the match expression
  // 4. Type errors cascade only through touched variables
}
```

**Key Insight**: Selective type-checking works automatically through context propagation:

```
File: math.tao

fn add(a, b) { a + b }          -- Loaded into context (unchecked)
fn mul(a, b) { a * b }          -- Loaded into context (unchecked)

> add(1, 2)                     -- Selected test
3                               -- Check this match expression

Result: 
- `add` is checked (touched by test)
- `mul` remains unchecked (not touched)
- Type errors in `mul` don't block this test
```

**How It Works**:

1. **Parse entire file** - Report all syntax errors immediately (syntax errors can cascade unpredictably)
2. **Load definitions into context** - All `fn`, `type`, `const` go into the type context but marked as unchecked
3. **Check test expression** - When checking `match example { result -> ... }`, the type checker follows variable references
4. **Automatic propagation** - Only definitions touched by the test get checked

**vs Full `check` Command**:

| Command | Behavior |
|---------|----------|
| `gleam run check src/` | Check ALL definitions, report ALL errors |
| `gleam run test src/ --match "add *"` | Syntax: check all. Types: check only `add *` tests + touched definitions |

**Implementation Approach**:

```gleam
// The core.infer() already does this - it only checks what it touches
// We just need to not fail early on unchecked definitions

pub fn check_test_expression(
  test: Test,
  context: TypeContext,  // All definitions loaded, unchecked
) -> CheckResult {
  // Create match expression: match test.expression { test.expected -> True }
  let match_expr = build_match_test(test)
  
  // Run core.infer() - it will only check what the expression touches
  let #(_value, _type, state) = core.infer(context, match_expr)
  
  // Return type errors (only from touched definitions)
  case state.errors {
    [] -> AllPassed
    errors -> HasErrors(errors)
  }
}
```

**Tasks**:
- [ ] Parse entire file, report all syntax errors
- [ ] Load all definitions into context (unchecked)
- [ ] Build match expression for each test
- [ ] Run `core.infer()` on test expression
- [ ] Collect type errors (only from touched code)
- [ ] Skip type-checking for `--no-check`

### Phase 4: Test Runner

**File**: `src/tao/test_runner.gleam`

```gleam
pub fn run_test(test: Test, state: State) -> TestResult {
  // Compile test expression to Core
  // Evaluate the expression
  // Match against expected pattern
  // Return Pass/Fail/Error
}

pub fn run_tests(tests: List(Test), state: State) -> List(TestResult) {
  // Run all tests (with optional parallelism)
}
```

**Tasks**:
- [ ] Compile test expression to Core term
- [ ] Type check (if not already checked)
- [ ] Evaluate the expression
- [ ] Pattern match against expected result
- [ ] Generate Pass/Fail/Error result
- [ ] Handle `@skip` tests (mark as Skipped)
- [ ] Handle `@timeout` (cancel if exceeds)

### Phase 5: CLI Integration

**File**: `src/compiler_bootstrap.gleam`

```gleam
pub type TestOptions {
  TestOptions(
    paths: List(String),
    match_patterns: List(String),
    list_only: Bool,
    verbose: Bool,
    debug: Bool,
    no_check: Bool,
  )
}

pub fn test_command(options: TestOptions) -> Nil {
  // 1. Discover all .tao files in paths
  // 2. Parse all files and extract tests
  // 3. Filter tests by patterns
  // 4. If --list, print names and exit
  // 5. Type-check only selected tests
  // 6. Run selected tests
  // 7. Report results
  // 8. Exit with appropriate code
}
```

**Tasks**:
- [ ] Add `test` subcommand to CLI parser
- [ ] Support multiple file/directory paths
- [ ] Recursive directory traversal
- [ ] Parse `--match`, `--list`, `--verbose`, `--no-check` options
- [ ] Integrate with existing check/run flow
- [ ] Exit code handling (0 = success, 1 = failure)

### Phase 6: Test Reporting

**File**: `src/tao/test_reporter.gleam`

```gleam
pub type TestSummary {
  TestSummary(
    total: Int,
    passed: Int,
    failed: Int,
    errors: Int,
    skipped: Int,
  )
}

pub fn report_results(
  results: List(TestResult),
  summary: TestSummary,
  verbose: Bool,
) -> Nil {
  // Print test results with colors
  // Show failures with expected vs got
  // Summary statistics
}
```

**Tasks**:
- [ ] Pass/fail summary (e.g., "42 passed, 2 failed")
- [ ] Failure details with expected vs got
- [ ] Color-coded output (green=pass, red=fail, yellow=skip)
- [ ] Verbose mode (show all tests, not just failures)
- [ ] Source snippets for failures
- [ ] Execution time per test (optional)

---

## Analysis and Improvements

### Key Insights

#### 1. Selective Type-Checking is Critical

**Problem**: Traditional test runners type-check everything before running any tests. This blocks iterative development during refactors.

**Solution**: Only type-check selected tests and their dependencies.

**Benefits**:
- Run tests for code you're changing, even if other parts are broken
- Fast feedback during large refactors
- Test-driven development without fixing entire codebase first

**Implementation Challenge**: Need to track dependencies between tests and definitions.

**Approach**: 
1. Parse entire file to get all definitions
2. For each selected test, find which definitions it references
3. Type-check only those definitions + the test
4. Skip everything else

#### 2. Test Filtering Enables Focused Development

**Use Cases**:
- `--match "parse *"` - Run all parser tests during parser refactor
- `--match "*addition*"` - Run all addition-related tests
- `--match "parse *" --match "eval *"` - Run multiple groups
- `--list` - Discover available tests

**Pattern Matching**: Simple wildcard (`*`) is sufficient for most cases. Regex is overkill.

#### 3. Examples as Documentation AND Tests

**Benefit**: Documentation never becomes outdated because it's the test itself.

**Trade-off**: Less flexibility than separate test framework (can't have setup/teardown blocks).

**Mitigation**: Future `@group` and `@skip` annotations provide some flexibility.

### Design Improvements

#### 1. Add `--only` Flag for Exact Match

```bash
# Run only the exact test named "integer addition"
gleam run test src/ --only "integer addition"
```

Useful for running a single test during debugging.

#### 2. Add `--exclude` Flag

```bash
# Run all tests except slow ones
gleam run test src/ --exclude "*slow*"
```

Complement to `--match`, allows excluding known problematic tests.

#### 3. Test Dependencies via `@requires`

```tao
-- @requires parse_integer
-- @requires parse_expression
> eval_expression()
result
```

For tests that depend on other tests passing first. Enables test ordering.

#### 4. Cached Type-Checking

For large files, cache type-check results:
```bash
gleam run test src/ --cache  # Use cached type-check results
```

Speeds up repeated test runs when only tests change, not definitions.

#### 5. Parallel Test Execution

Independent tests can run in parallel:
```gleam
// In test_runner.gleam
pub fn run_tests_parallel(tests: List(Test), state: State) -> List(TestResult) {
  // Use gleam's async/concurrency primitives
}
```

**Challenge**: Need to ensure tests don't share mutable state.

### Known Challenges

#### 1. Syntax Errors vs Type Errors

**Key Distinction**:

| Error Type | Reporting | Rationale |
|------------|-----------|-----------|
| **Syntax errors** | Always report (all files) | Can cascade unpredictably, block parsing |
| **Type errors** | Only report for selected tests | Automatically isolated via context propagation |

**Implementation**:
```gleam
pub fn test_command(options: TestOptions) -> Nil {
  // 1. Parse ALL files, collect ALL syntax errors
  let parse_results = parse_all_files(options.paths)
  let syntax_errors = collect_syntax_errors(parse_results)
  
  // 2. Report syntax errors (always)
  report_syntax_errors(syntax_errors)
  
  // 3. Extract tests and filter
  let all_tests = extract_tests(parse_results)
  let selected_tests = filter_tests(all_tests, options.match_patterns)
  
  // 4. Type-check ONLY selected tests (selective)
  let type_results = check_selected_tests(selected_tests, parse_results)
  
  // 5. Run tests regardless of type errors
  let test_results = run_tests(selected_tests)
  
  // 6. Report and exit
  report_results(test_results, type_results)
}
```

#### 2. Multi-line Expression Parsing

**Problem**: Need to distinguish between:
```tao
-- Test 1
> let x = 1
> let y = 2
> x + y
3

-- Test 2
> single_line()
result
```

**Solution**: Lines starting with `> ` continue the expression. Blank line or `-- ` starts new test.

#### 3. Pattern Matching Complexity

**Problem**: Expected results are patterns, not just values. Need to implement pattern matching.

**Example**:
```tao
> Some(42)
Some(_)  // Pattern, not value
```

**Solution**: Reuse existing Core pattern matching infrastructure. The expected result parses as a `Pattern`, not a `Term`.

#### 4. Error Localization

**Problem**: When a test fails, show exactly where and why.

**Solution**: Include span information in `TestResult`:
```gleam
Fail(span: Span, name: String, expected: String, got: String)
```

Format with source snippet:
```
❌ FAIL: integer addition
   ┌─ src/math.tao:5:1
   │
 5 │ > 1 + 2
   │   ^^^^^
   │
   = expected: 3
   = got:      4
```

#### 5. Parallel Execution with Ordered Output

**Challenge**: Tests can run in parallel for speed, but output should be deterministic.

**Solution**:
```gleam
pub fn run_tests_parallel(tests: List(Test), state: State) -> List(TestResult) {
  // 1. Run tests in parallel (by index)
  let results_with_index = run_parallel(indexed_tests)
  
  // 2. Sort results by original index
  let sorted_results = sort_by_index(results_with_index)
  
  // 3. Report in order
  report_results(sorted_results)
}
```

**Benefit**: Fast execution + predictable output for debugging.

---

## Design Decisions

### Why REPL-like Syntax?

**Pros**:
- Examples double as tests (no duplication)
- Easy to read and write
- Familiar to developers
- Documentation stays in sync with tests

**Cons**:
- Less flexible than traditional test frameworks
- Pattern matching may be confusing for beginners

**Decision**: **Use REPL-like syntax** - benefits outweigh drawbacks. Can add flexibility later with annotations.

### Why Continue on Check Errors?

**Options**:
- A: Fail immediately on any check error
- B: Continue running tests despite check errors (current plan)
- C: Configurable via `--fail-fast` flag

**Decision**: **Option B** with **Option C** as future enhancement.

**Rationale**:
1. Partial testing - Some tests may still pass
2. Iterative development - Test while fixing errors
3. Consistency - Same behavior as `run` command
4. Selective checking - Only check selected tests anyway

### Why Patterns for Expected Results?

**Benefits**:
- Test opaque types: `Some(_)`
- Partial matches: `{a = _, b = 2}`
- List lengths: `[_, _, _]`
- Type-level assertions: `#Ok(_)` vs `#Error(_)`

**Decision**: **Use patterns** - more expressive than value equality.

### Why Wildcard Matching Instead of Regex?

**Options**:
- Wildcards: `"parse *"` (simple)
- Regex: `"parse.*"` (powerful but complex)

**Decision**: **Wildcards** - sufficient for 95% of use cases, simpler to implement and understand.

**Future**: Can add regex via `--match-regex` if needed.

### Why Not Require File to Compile First?

**Traditional approach**:
```bash
# Must fix ALL errors before running ANY tests
gleam build && gleam test
```

**Our approach**:
```bash
# Run tests even with errors in unrelated code
gleam run test src/ --match "parse *"
```

**Decision**: **Don't require full compilation** - enables iterative development.

---

## Alternatives Considered

### Alternative 1: Traditional Test Framework

```tao
@test("integer addition")
fn test_add() {
  assert(1 + 2 == 3)
}
```

**Rejected because**:
- More verbose
- Separates examples from tests
- Requires function syntax
- Doesn't serve as documentation

### Alternative 2: Comment Annotations

```tao
// test: 1 + 2 = 3
1 + 2
```

**Rejected because**:
- Less readable
- Harder to parse multi-line
- Doesn't look like documentation
- Inline syntax clutters code

### Alternative 3: Separate Test Files

```tao
// src/math.tao
pub fn add(a, b) { a + b }

// test/math_test.tao
import math
test add(1, 2) == 3
```

**Rejected because**:
- Duplication between code and tests
- Tests can become outdated
- More files to manage
- Can't see examples with implementation

### Alternative 4: Full Compilation Required

```bash
# Must compile before testing
gleam build
gleam test
```

**Rejected because**:
- Blocks iterative development
- Can't test during refactors
- Slow feedback loop

---

## Open Questions

### 1. Should `--match` Apply to File Names Too?

**Decision**: ✅ **Yes, match both filename and test name**

```bash
# Matches:
# - Tests named "parse *" in any file
# - Any test in a file named "parse*.tao"
gleam run test src/ --match "parse *"
```

**Implementation**:
```gleam
pub fn matches_pattern(pattern: String, test: Test, file: String) -> Bool {
  // Check test name
  let name_match = wildcard_match(pattern, test.name)
  
  // Check filename (extract base name without extension)
  let file_base = file_base_name(file)  // "parser.tao" -> "parser"
  let file_match = wildcard_match(pattern, file_base)
  
  name_match || file_match
}
```

### 2. Should Tests Run in Order?

**Decision**: ✅ **Parallel execution, ordered output**

- Tests run in parallel for speed
- Output is sorted by original index for deterministic reporting
- Dependencies can be added later via `@requires` if real cases arise

### 3. How to Handle IO Tests?

**Decision**: ⏳ **Leave open** - IO not yet implemented

Options when IO is implemented:
- Mark IO tests with `@io` and skip by default
- Mock IO via test context
- Don't support IO tests (pure functions only)

### 4. Should There Be a Test Timeout?

**Decision**: ✅ **Yes, configurable timeout**

```tao
-- @timeout 5000  -- 5 seconds (default)
> slow_operation()
result

-- @timeout 30000  -- 30 seconds for slow tests
> very_slow_operation()
result
```

**Default**: 5 seconds per test

### 5. How to Handle Flaky Tests?

**Decision**: ⏳ **Leave open** - Requires decorator planning

**Options**:
- Retry mechanism (`@retry 3`)
- Mark as flaky and skip
- Fail immediately (recommended for now)

**Note**: Retry mechanism would require decorators to be implementable in libraries. This needs more planning.

---

## Resolved Questions

### 6. Should Check Errors Cause Test Failure?

**Decision**: ✅ **No, run tests regardless (like `run` command)**

- Type errors in selected tests are reported but don't block execution
- Syntax errors are always reported (can cascade unpredictably)
- Exit code 1 if there are type errors OR test failures

### 7. How to Handle Test Dependencies?

**Decision**: ✅ **No order guarantee (parallel-safe), add `@requires` later if needed**

- Tests run in parallel by default
- Can add `@requires` annotation later if real dependency cases arise
- For now, tests should be independent

---

## Testing Strategy

### Unit Tests

- [ ] Test parser with various syntax formats
- [ ] Test wildcard pattern matching
- [ ] Test filter logic (OR, multiple patterns)
- [ ] Test pattern matching for expected results
- [ ] Test result generation (Pass, Fail, Error, Skipped)

### Integration Tests

- [ ] End-to-end test command
- [ ] Directory traversal
- [ ] Error reporting with source snippets
- [ ] Selective type-checking
- [ ] Exit codes

### Dogfooding

- [ ] Use test system to test itself
- [ ] Convert existing examples to tests
- [ ] All new features must have tests

---

## Future Work

### Phase 1 (Post-MVP)

- [ ] `@skip` annotation support
- [ ] `@timeout` annotation support
- [ ] `@group` annotation support
- [ ] `--exclude` flag
- [ ] `--only` flag (exact match)

### Phase 2 (Advanced)

- [ ] Test parallelization
- [ ] Test coverage reporting
- [ ] Watch mode for TDD
- [ ] Cached type-checking
- [ ] `@requires` for test dependencies

### Phase 3 (Experimental)

- [ ] Snapshot testing
- [ ] Property-based testing
- [ ] Fuzzing
- [ ] Visual test runner (TUI)

---

## Change Log

| Date | Change |
|------|--------|
| March 14, 2026 | Initial plan created |
| March 14, 2026 | Added selective type-checking design |
| March 14, 2026 | Added test filtering with wildcards |
| March 14, 2026 | Added analysis and improvements section |
| March 14, 2026 | Added `--list`, `--exclude`, `--only` options |
| March 14, 2026 | Added test annotations (@skip, @timeout, @group, @requires) |
| March 14, 2026 | Documented known challenges and solutions |
| March 14, 2026 | **Updated selective type-checking**: Syntax errors always reported, type errors selective via context propagation |
| March 14, 2026 | **Resolved open questions**: `--match` matches files+tests, parallel exec with ordered output, configurable timeout |
| March 14, 2026 | **Left open**: IO tests (not implemented), flaky test retry (needs decorator planning) |
