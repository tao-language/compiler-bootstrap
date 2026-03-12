# E2E Test Enhancement Plan

> **Goal**: Enhance E2E tests with full golden file comparison for both success and error cases
> **Status**: 🔄 In Progress
> **Date**: March 11, 2026
> **Priority**: High

---

## Overview

The current E2E test system successfully:
- ✅ Auto-discovers all `.core.tao` files
- ✅ Groups tests by category (programs, terms, errors)
- ✅ Validates success/failure expectations
- ✅ Reports detailed errors with formatted output

**What's missing:**
- ❌ Success tests only check for "OK" (not actual NbE output)
- ❌ Error tests only check for "ERROR" (not actual error messages)
- ❌ No regression protection for output format changes
- ❌ Golden files are placeholders, not real expected output

---

## Enhancement Goals

### Goal 1: Full Output Comparison for Success Cases

**Current behavior:**
```
Expected: "OK"
Actual: (ignored)
```

**Target behavior:**
```
Expected: "✓ Type checking input\n✓ Evaluating...\nResult: x -> x"
Actual: "✓ Type checking input\n✓ Evaluating...\nResult: x -> x"
```

**Benefits:**
- Catches regressions in NbE output format
- Documents expected output for each example
- Ensures CLI output remains stable

### Goal 2: Full Error Message Comparison

**Current behavior:**
```
Expected: "ERROR"
Actual: (ignored)
```

**Target behavior:**
```
Expected: "❌ error[E0101]: Type mismatch\n   ┌─ input:3:5\n   ..."
Actual: "❌ error[E0101]: Type mismatch\n   ┌─ input:3:5\n   ..."
```

**Benefits:**
- Catches regressions in error message quality
- Ensures error codes, spans, and hints remain stable
- Documents expected error messages for common mistakes

### Goal 3: Golden File Generation Tool

**Purpose**: Make it easy to update golden files when output changes intentionally

**Features:**
- `--update-golden` flag to regenerate all golden files
- `--update-golden <pattern>` to update specific examples
- Dry-run mode to show what would change

---

## Implementation Plan

### Phase 1: Update Test Infrastructure

#### Task 1.1: Update `run_example` Function

**Current:**
```gleam
fn run_example(example: Example) -> Bool {
  // ...
  case string.trim(expected) {
    "OK" -> False  // Test passed
    other -> True  // Test failed
  }
}
```

**Target:**
```gleam
fn run_example(example: Example) -> Bool {
  // ...
  case example.category {
    ShouldSucceed -> {
      let actual_output = format_success_output(value, quoted, typ)
      compare_output(actual_output, expected, example.path)
    }
    ShouldFail -> {
      let actual_output = format_errors(all_errors, source, example.path)
      compare_output(actual_output, expected, example.path)
    }
  }
}
```

#### Task 1.2: Implement Output Formatting

**Success output format:**
```
✓ Type checking input
✓ Evaluating...
Result: <quoted_term>
```

**Error output format:**
```
<formatted_error_1>
<formatted_error_2>
...
```

#### Task 1.3: Implement Term Quoting for Output

Need to convert `Term` back to readable syntax:
```gleam
fn quote_to_string(term: Term) -> String {
  case term {
    Var(name, _) -> name
    Lam(name, body, _) -> name <> " -> " <> quote_to_string(body)
    App(fun, arg, _) -> quote_to_string(fun) <> "(" <> quote_to_string(arg) <> ")"
    // ... etc
  }
}
```

### Phase 2: Generate Golden Files

#### Task 2.1: Create Generation Script

```bash
#!/bin/bash
# scripts/update_golden_files.sh

for file in examples/core/programs/*.core.tao; do
  output="${file%.core.tao}.output.txt"
  gleam run run "$file" > "$output" 2>&1
done

for file in examples/core/errors/*/*.core.tao; do
  output="${file%.core.tao}.output.txt"
  gleam run check "$file" > "$output" 2>&1
done
```

#### Task 2.2: Generate All Golden Files

Run the script to generate golden files for all examples.

#### Task 2.3: Review and Clean Up

- Remove ANSI codes from golden files (or keep them?)
- Normalize paths in error messages
- Ensure stable output (no timestamps, random IDs)

### Phase 3: Update Documentation

#### Task 3.1: Update E2E Test Plan

Mark `docs/plans/testing/e2e-test-plan.md` as ✅ Complete with notes.

#### Task 3.2: Add to README

Document:
- How to run E2E tests
- How to add new examples
- How to update golden files

#### Task 3.3: Create Golden File Guide

Document:
- Golden file format
- When to update golden files
- How to review golden file changes

---

## Technical Considerations

### ANSI Color Codes

**Option A**: Strip ANSI codes from golden files
- ✅ Cleaner diffs
- ✅ Platform-independent
- ❌ Doesn't test color output

**Option B**: Keep ANSI codes in golden files
- ✅ Tests color output
- ❌ Messier diffs
- ❌ May vary by terminal

**Recommendation**: Strip ANSI codes for golden files, test colors separately.

### Path Normalization

Error messages include file paths. These should be normalized:
- Use relative paths from project root
- Or use placeholder like `input` for all examples

**Recommendation**: Use `input` as the filename for all examples to keep golden files portable.

### Span Stability

Error spans depend on source code. These are stable as long as examples don't change.

**Action**: Document that changing example source requires updating golden files.

---

## Success Criteria

- [ ] All success examples compare actual NbE output
- [ ] All error examples compare actual error messages
- [ ] Golden file generation script works
- [ ] Documentation updated
- [ ] All tests pass with new comparison logic
- [ ] CI pipeline updated (if applicable)

---

## Risks and Mitigations

### Risk 1: Output Format Changes Frequently

**Mitigation**: 
- Stabilize output format before generating golden files
- Document what parts of output are stable vs. may change

### Risk 2: Golden Files Become Outdated

**Mitigation**:
- Make golden file updates easy with script
- Add CI check that fails if golden files are missing

### Risk 3: Tests Become Brittle

**Mitigation**:
- Only compare stable parts of output
- Use substring matching for parts that may vary (e.g., span details)

---

## Timeline

| Phase | Tasks | Estimated Time |
|-------|-------|----------------|
| Phase 1 | Update test infrastructure | 2-3 hours |
| Phase 2 | Generate golden files | 1 hour |
| Phase 3 | Update documentation | 30 minutes |
| **Total** | | **4-5 hours** |

---

## Related Plans

- ✅ `docs/plans/testing/e2e-test-plan.md` - Original E2E test implementation
- 🔄 `docs/plans/error-reporting/02-error-types.md` - Error type coverage
- 🔄 `docs/plans/error-reporting/03-source-snippets.md` - Source snippet formatting

---

## Notes

- This enhancement makes the E2E test suite a **regression prevention tool**, not just a sanity check
- Golden files serve as **living documentation** of expected behavior
- Easy golden file updates prevent tests from becoming a burden
