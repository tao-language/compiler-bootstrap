# Enhanced Test Framework Implementation Plan

**Date**: 2026-03-17  
**Status**: 📋 **Planned**  
**Priority**: Medium - Improves developer experience  
**Estimated Time**: 2-3 hours

---

## Overview

Enhance the Tao test framework with proper test reporting, pass/fail counts, and improved CLI integration.

**Current State**:
- ✅ Test parser exists (`src/tao/test_parser.gleam`)
- ✅ Test filter exists (`src/tao/test_filter.gleam`)
- ✅ Test runner exists (`src/tao/test_runner.gleam`)
- ⚠️ CLI test command exists but basic reporting

**Goal**: Professional test output with summary, colors, and clear failure reporting.

---

## Features to Implement

### 1. Test Summary with Counts

**Current**: Basic result list

**Enhanced**:
```
Running tests...

✓ Test: addition (2ms)
✓ Test: subtraction (1ms)
✗ Test: multiplication
    Expected: 6
    Got:      5
    At:       src/math.tao:5:1

────────────────────────────────────────
Test Summary:
  Total:     10
  Passed:    8
  Failed:    2
  Skipped:   0
  Errors:    0

✗ Some tests failed
```

### 2. Color-Coded Output

| Color | Meaning |
|-------|---------|
| Green (✓) | Test passed |
| Red (✗) | Test failed |
| Yellow (○) | Test skipped |
| Red (⚠) | Runtime error |

### 3. Source Snippets for Failures

```
✗ FAIL: multiplication
   ┌─ src/math.tao:5:1
   │
 5 │ > 2 * 3
   │   ^^^^^
   │
   = expected: 6
   = got:      5
```

### 4. Verbose Mode

```bash
# Default: show only failures
gleam run test src/

# Verbose: show all tests
gleam run test src/ --verbose
```

### 5. Test Execution Time

```
✓ Test: addition (2ms)
✓ Test: complex_calculation (47ms)
⚠ Test: slow_operation (5002ms) - exceeded timeout
```

---

## Implementation Plan

### Phase 1: Update TestResult Type (30 min)

**File**: `src/tao/test_runner.gleam`

Add execution time and improve result structure:

```gleam
pub type TestResult {
  Pass(
    test_item: Test,
    result: Value,
    duration_ms: Int,
  )
  Fail(
    test_item: Test,
    expected: String,
    got: String,
    duration_ms: Int,
  )
  Error(
    test_item: Test,
    message: String,
    duration_ms: Int,
  )
  Skipped(
    test_item: Test,
    reason: String,
  )
  TimedOut(
    test_item: Test,
    timeout_ms: Int,
    duration_ms: Int,
  )
}
```

### Phase 2: Implement Test Summary (30 min)

**File**: `src/tao/test_runner.gleam`

Add summary calculation:

```gleam
pub type TestSummary {
  TestSummary(
    total: Int,
    passed: Int,
    failed: Int,
    skipped: Int,
    timed_out: Int,
    errored: Int,
    total_duration_ms: Int,
  )
}

pub fn calculate_summary(results: List(TestResult)) -> TestSummary {
  // Count by result type
}

pub fn get_failures(results: List(TestResult)) -> List(TestResult) {
  // Filter to only failures and errors
}

pub fn all_passed(results: List(TestResult)) -> Bool {
  // Check if all tests passed
}
```

### Phase 3: Enhanced Test Reporter (1 hour)

**File**: `src/tao/test_reporter.gleam` (new)

Create dedicated reporter module:

```gleam
import gleam/io
import syntax/error_reporter

pub fn report_results(
  results: List(TestResult),
  summary: TestSummary,
  verbose: Bool,
  source: String,
) -> Nil {
  // Print each result
  list.each(results, fn(result) {
    case verbose {
      True -> report_result_verbose(result)
      False -> report_result_condensed(result)
    }
  })

  // Print summary
  report_summary(summary)
}

fn report_result_verbose(result: TestResult) -> Nil {
  case result {
    Pass(test, _, duration) -> {
      io.println("✓ Test: " <> test.name <> " (" <> int.to_string(duration) <> "ms)")
    }
    Fail(test, expected, got, duration) -> {
      io.println("✗ Test: " <> test.name)
      io.println("    Expected: " <> expected)
      io.println("    Got:      " <> got)
      io.println("    Duration: " <> int.to_string(duration) <> "ms")
    }
    // ... etc
  }
}

fn report_summary(summary: TestSummary) -> Nil {
  io.println("────────────────────────────────────────")
  io.println("Test Summary:")
  io.println("  Total:     " <> int.to_string(summary.total))
  io.println("  Passed:    " <> int.to_string(summary.passed))
  io.println("  Failed:    " <> int.to_string(summary.failed))
  io.println("  Skipped:   " <> int.to_string(summary.skipped))
  io.println("  Errors:    " <> int.to_string(summary.errored))
  io.println("  Duration:  " <> int.to_string(summary.total_duration_ms) <> "ms")
}
```

### Phase 4: CLI Integration (30 min)

**File**: `src/compiler_bootstrap.gleam`

Update test command to use new reporter:

```gleam
fn run_test_command(
  paths: List(String),
  match_pattern: String,
  list_tests: Bool,
  verbose: Bool,
  debug: Bool,
) -> Nil {
  // 1. Parse files
  let test_files = discover_test_files(paths)
  let all_tests = parse_test_files(test_files)

  // 2. Filter tests
  let filtered_tests = filter_tests(all_tests, match_pattern)

  // 3. List mode
  case list_tests {
    True -> {
      list_tests(filtered_tests)
      return
    }
    False -> Nil
  }

  // 4. Run tests
  let results = run_tests(filtered_tests)
  let summary = calculate_summary(results)

  // 5. Report results
  report_results(results, summary, verbose, "")

  // 6. Exit with appropriate code
  case all_passed(results) {
    True -> io.println("✓ All tests passed!")
    False -> {
      io.println("✗ Some tests failed")
      // Exit code 1
    }
  }
}
```

### Phase 5: Source Snippets (30 min)

**Integration**: Use existing `syntax/error_reporter` module

```gleam
fn report_failure_with_snippet(
  test: Test,
  expected: String,
  got: String,
  source: String,
) -> Nil {
  // Create diagnostic
  let diagnostic = error_reporter.Diagnostic(
    severity: Error,
    title: "Test failed: " <> test.name,
    message: "Expected " <> expected <> " but got " <> got,
    snippets: [
      error_reporter.SourceSnippet(
        source: source,
        span: test.span,
      )
    ],
  )

  // Format and print
  let formatted = error_reporter.format_diagnostic(diagnostic)
  io.println(formatted)
}
```

---

## Files to Create/Modify

### New Files
- `src/tao/test_reporter.gleam` - Enhanced test reporting

### Modified Files
- `src/tao/test_runner.gleam` - Add duration tracking, summary
- `src/compiler_bootstrap.gleam` - Integrate new reporter
- `test/tao/test_runner_test.gleam` - Add tests for new features

---

## Test Cases

### Summary Calculation

```gleam
pub fn calculate_summary_test() {
  let results = [
    Pass(test1, value1, 10),
    Pass(test2, value2, 20),
    Fail(test3, "6", "5", 15),
    Skipped(test4, "not implemented"),
  ]

  let summary = calculate_summary(results)

  summary.total |> should.equal(4)
  summary.passed |> should.equal(2)
  summary.failed |> should.equal(1)
  summary.skipped |> should.equal(1)
  summary.errored |> should.equal(0)
  summary.total_duration_ms |> should.equal(45)
}
```

### Verbose Output

```gleam
pub fn report_verbose_shows_all_tests() {
  // Capture stdout
  // Run report_results with verbose=True
  // Verify all tests are shown
}
```

### Condensed Output

```gleam
pub fn report_condensed_shows_failures_only() {
  // Capture stdout
  // Run report_results with verbose=False
  // Verify only failures are shown
}
```

---

## Success Criteria

- [ ] Test summary shows correct counts
- [ ] Verbose mode shows all tests
- [ ] Condensed mode shows only failures
- [ ] Source snippets displayed for failures
- [ ] Exit code is correct (0=pass, 1=fail)
- [ ] All existing tests still pass
- [ ] New reporter tests pass

---

## Future Enhancements

### Post-MVP Features

1. **Color Output**
   - ANSI color codes for ✓/✗
   - Configurable via `--no-color`

2. **Parallel Execution**
   - Run tests in parallel
   - Sort output by original order

3. **Watch Mode**
   - Re-run tests on file changes
   - `gleam run test --watch`

4. **Test Coverage**
   - Track which code is tested
   - Coverage report

5. **JUnit/XML Output**
   - CI/CD integration
   - `--format junit`

---

## References

- [Original Test System Plan](11-test-system.md) - Full test system specification
- [Tao Status](tao-status.md) - Current Tao implementation status
- [Session Summary](../session-summary-2026-03-17.md) - Current session progress

---

**Status**: Ready to implement  
**Next**: Phase 1 - Update TestResult type
