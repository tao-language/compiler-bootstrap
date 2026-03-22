# Source Snippets for Test Failures

**Date**: 2026-03-17  
**Status**: 📋 **Planned**  
**Priority**: High - Improves debugging experience  
**Estimated Time**: 1-2 hours

---

## Overview

Add source code snippets to test failure output, showing the exact location and context of failures.

**Current Output**:
```
✗ FAIL: multiplication
    Expected: 6
    Got:      5
```

**Enhanced Output**:
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

---

## Requirements

### 1. Source Snippet Display

Show the failing test's source code with:
- File path and line number
- Source code line(s)
- Caret (^) pointing to the expression
- Expected vs got values

### 2. Integration with Existing Infrastructure

Reuse the existing `syntax/error_reporter` module for consistent formatting.

### 3. Source Code Access

Need access to source code when running tests. Currently tests are parsed from strings, but we need to preserve the source for snippet display.

---

## Implementation Plan

### Phase 1: Update TestResult to Include Source (30 min)

**File**: `src/tao/test_runner.gleam`

Add source and span information to failure results:

```gleam
pub type TestResult {
  Pass(
    test_item: Test,
    result: Value,
  )
  Fail(
    test_item: Test,
    expected: String,
    got: String,
    source: String,      // NEW: Full source code
  )
  Error(
    test_item: Test,
    message: String,
    source: String,      // NEW: Full source code
  )
  Skipped(test_item: Test, reason: String)
  TimedOut(test_item: Test, timeout_ms: Int)
}
```

### Phase 2: Update Test Runner to Capture Source (30 min)

**File**: `src/tao/test_runner.gleam`

Pass source code through to results:

```gleam
pub fn run_tests(tests: List(Test), source: String) -> List(TestResult) {
  list.map(tests, fn(test) {
    run_single_test(test, source)
  })
}

fn run_single_test(test_item: Test, source: String) -> TestResult {
  // ... existing logic ...
  case values_equal(value, expected_value) {
    True -> Pass(test_item, value)
    False -> {
      let got_str = format_value(value)
      let expected_str = format_value(expected_value)
      Fail(test_item, expected_str, got_str, source)  // Include source
    }
  }
}
```

### Phase 3: Update Reporter to Display Snippets (30 min)

**File**: `src/tao/test_reporter.gleam`

Use `syntax/error_reporter` to format snippets:

```gleam
fn report_failure_with_snippet(
  test: Test,
  expected: String,
  got: String,
  source: String,
) -> Nil {
  io.println("✗ FAIL: " <> test.name)
  
  // Create diagnostic with snippet
  let diagnostic = error_reporter.type_error_to_diagnostic(
    test.span,
    source,
    "Test failed",
    "Expected " <> expected <> " but got " <> got,
  )
  
  // Format and print
  let formatted = error_reporter.format_diagnostic(diagnostic)
  io.println(formatted)
  
  // Also show expected/got
  io.println("    Expected: " <> expected)
  io.println("    Got:      " <> got)
  io.println("")
}
```

### Phase 4: Update CLI Integration (15 min)

**File**: `src/compiler_bootstrap.gleam`

Pass source code to test runner:

```gleam
fn run_and_report_tests(tests_with_files: List(#(List(Test), String)), verbose: Bool) -> Nil {
  list.each(tests_with_files, fn(pair) {
    let #(tests, source) = pair
    let results = run_tests(tests, source)  // Pass source
    // ... report results
  })
}
```

### Phase 5: Add Tests (30 min)

**File**: `test/tao/test_reporter_test.gleam`

Test snippet formatting:

```gleam
pub fn test_failure_shows_snippet() {
  let source = "> 2 * 3\n6"
  let test = Test("multiplication", expr, expected, span, [])
  let result = Fail(test, "6", "5", source)
  
  // Capture output
  // Verify snippet is displayed
}
```

---

## Files to Create/Modify

### New Files
- `test/tao/test_reporter_test.gleam` - Tests for reporter

### Modified Files
- `src/tao/test_runner.gleam` - Add source to results
- `src/tao/test_reporter.gleam` - Display snippets
- `src/compiler_bootstrap.gleam` - Pass source to runner

---

## Design Decisions

### How Much Source to Show?

**Options**:
- A: Single line (just the failing expression)
- B: 3 lines (one before, the failing line, one after)
- C: Full test (from `>` to expected result)

**Decision**: **Option B** - 3 lines provides context without clutter.

### Caret Width

**Options**:
- A: Single caret (`^`)
- B: Width of expression (`^^^^^`)
- C: Full line underline

**Decision**: **Option B** - Matches expression width for precision.

### Color Support

**Options**:
- A: No color (plain text)
- B: ANSI colors (green/red/yellow)
- C: Configurable via `--color` flag

**Decision**: **Option B** with future **Option C** - Colors improve readability, can add flag later.

---

## Error Reporter Integration

The existing `syntax/error_reporter.gleam` provides:

```gleam
pub fn type_error_to_diagnostic(
  error: TypeError,
  source: String,
  file: String,
) -> source_snippet.Diagnostic
```

We need a simpler version for test failures:

```gleam
pub fn test_failure_to_diagnostic(
  span: Span,
  source: String,
  file: String,
  title: String,
  message: String,
) -> source_snippet.Diagnostic {
  source_snippet.Diagnostic(
    severity: Error,
    title: title,
    message: message,
    snippets: [
      source_snippet.SourceSnippet(
        source: source,
        span: span,
        label: Some("this test failed"),
      )
    ],
  )
}
```

---

## Test Cases

### Basic Failure with Snippet

```gleam
pub fn test_basic_failure_snippet() {
  let source = "-- multiplication\n> 2 * 3\n6"
  let span = Span("test.tao", 2, 1, 2, 6)  // Line 2, columns 1-6
  
  let result = run_test(source, span)
  
  // Should show:
  // ✗ FAIL: multiplication
  //    ┌─ test.tao:2:1
  //    │
  //  2 │ > 2 * 3
  //    │   ^^^^^
  //    │
  //    = expected: 6
  //    = got:      5
}
```

### Multi-line Expression

```gleam
pub fn test_multiline_expression_snippet() {
  let source = "-- complex calc\n> let x = 1\n> let y = 2\n> x + y\n3"
  
  // Should show all lines of the expression
}
```

### Error with Snippet

```gleam
pub fn test_error_snippet() {
  let source = "-- division by zero\n> 1 / 0\nError"
  
  // Should show:
  // ⚠ ERROR: division by zero
  //    ┌─ test.tao:2:1
  //    │
  //  2 │ > 1 / 0
  //    │   ^^^^^
  //    │
  //    = Message: Division by zero
}
```

---

## Success Criteria

- [ ] Failures show source snippet with file:line:col
- [ ] Caret points to exact expression location
- [ ] Expected/got values displayed below snippet
- [ ] Errors also show snippets
- [ ] Multi-line expressions handled correctly
- [ ] All existing tests still pass
- [ ] New snippet tests pass

---

## Future Enhancements

### Post-MVP Features

1. **Color Output**
   - Red for failures
   - Yellow for errors
   - Green for passed (in verbose mode)

2. **Context Lines**
   - Show 2 lines before/after failure
   - Configurable via `--context <n>` flag

3. **Diff View**
   - Side-by-side expected vs got
   - Highlight differences

4. **Quick Fix Suggestions**
   - "Did you mean: 2 + 3?" for common mistakes

---

## References

- [Enhanced Test Framework Plan](enhanced-test-framework-plan.md) - Parent plan
- [Error Reporter](../../src/syntax/error_reporter.gleam) - Existing snippet formatting
- [Source Snippet Library](../../src/syntax/source_snippet.gleam) - Low-level snippet logic

---

**Status**: Ready to implement  
**Next**: Phase 1 - Update TestResult type
