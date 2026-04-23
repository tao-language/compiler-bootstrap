# Wildcard Pattern Exhaustiveness Bug - Fix Plan and Retrospective

> **Date**: March 2026 (Updated)
> **Status**: 🐛 Root Cause Identified (Grammar Structure Mismatch)
> **Test Status**: 520/522 tests passing (99.6%)
> **Severity**: High - prevents wildcard patterns from working

---

## Executive Summary

**Root Cause**: The bug is in the **grammar structure** for `PrimaryPattern` rules. The use of `seq([token_pattern()])` causes the grammar to wrap results incorrectly, leading to pattern extraction finding the wrong AstValue.

**Key Finding from Debug Logging**:
```
DEBUG after_pipe: A,T(->),A
DEBUG found AstValue: Int(0)
DEBUG extracted pattern: PLit(0)
```

The clause structure is correct (`AstValue, Arrow, AstValue`), but the first `AstValue` contains `Int(0)` instead of `Var("_", ...)`. This indicates the grammar is producing the wrong expression for the wildcard pattern.

**Fix Applied**: Changed `PrimaryPattern` rules from `seq([token_pattern()])` to `token_pattern()` directly, with proper value handling in the function.

**Current Status**: Fix applied but verification pending. The wildcard and variable pattern examples still fail, suggesting additional issues.

---

## Implementation Status

- [x] Phase 1: Add debug logging
- [x] Phase 2: Identify source of wrong pattern (grammar structure issue)
- [x] Phase 3: Fix pattern extraction logic (changed seq() to direct token_pattern())
- [x] Phase 4: Simplify extraction logic (find_first_ast_value)
- [ ] Phase 5: Verify fix for all pattern types (IN PROGRESS - still failing)

---

## Key Changes Made

### 1. Simplified Pattern Extraction

**Before**:
```gleam
fn extract_pattern_from_clause_items(items, pipe_pos) {
  let pattern_items = list.drop(items, pipe_pos + 1) |> list.take(1)
  case pattern_items {
    [AstValue(expr)] -> pattern_ast_to_pattern(expr)
    [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
    // ... multiple cases
    _ -> find_any_pattern(look_ahead)  // Searches too broadly
  }
}
```

**After**:
```gleam
fn extract_pattern_from_clause_items(items, pipe_pos) {
  let after_pipe = list.drop(items, pipe_pos + 1)
  find_first_ast_value(after_pipe) |> pattern_ast_to_pattern
}

fn find_first_ast_value(items) {
  case items {
    [AstValue(e), ..] -> e  // Found it!
    [TokenValue(_), ..rest] -> find_first_ast_value(rest)  // Skip tokens
    [KeywordValue(_), ..rest] -> find_first_ast_value(rest)  // Skip keywords
    [ListValue(_), ..rest] -> find_first_ast_value(rest)  // Skip nested (guards/body)
    [_, ..rest] -> find_first_ast_value(rest)
  }
}
```

**Rationale**: The new implementation only searches at the top level, avoiding finding AstValue from unrelated expressions (like the body or guard).

### 2. Fixed PrimaryPattern Grammar

**Before**:
```gleam
alt(
  seq([token_pattern("Underscore")]),
  fn(_) { Var("_", Span("_", 0, 0, 0, 0)) },
)
```

**After**:
```gleam
alt(
  token_pattern("Underscore"),
  fn(values) {
    case values {
      [TokenValue(_)] -> Var("_", Span("_", 0, 0, 0, 0))
      _ -> Var("_", Span("error", 0, 0, 0, 0))
    }
  },
)
```

**Rationale**: Using `token_pattern()` directly (without `seq()`) ensures correct wrapping by `alt()`.

### 3. Fixed Integer Reference

**Before**:
```gleam
alt(
  seq([ref("Integer")]),  // Integer rule doesn't exist!
  fn(values) { ... }
)
```

**After**:
```gleam
alt(
  token_pattern("Number"),  // Use actual token name
  fn(values) { ... }
)
```

**Rationale**: `ref("Integer")` referenced a non-existent rule, causing silent failures.

---

## Retrospective: How Debugging Could Have Been Easier

### What Went Wrong

1. **Lack of Unit Tests for Pattern Extraction**
   - No tests for `extract_*` functions
   - Bug could have been caught immediately

2. **Complex Grammar Structure**
   - `seq([token_pattern()])` vs `token_pattern()` produces different wrapping
   - Hard to predict without debugging

3. **No Grammar Structure Documentation**
   - No examples of expected output structure
   - Had to reverse-engineer through debugging

4. **Silent Failures**
   - `ref("Integer")` to non-existent rule falls back to `Int(0)`
   - No error or warning

### Lessons Learned

1. **Test Every Function That Transforms Data**
   - Especially `extract_*` and `to_*` functions

2. **Understand Grammar Library Behavior**
   - `seq()` wraps in `ListValue`
   - `alt()` wraps function results in `AstValue`
   - Document these behaviors

3. **Add Debug Logging Early**
   - Include context (file, line, expression)
   - Make logging easy to enable/disable

4. **Use Simpler Grammar Structures**
   - Avoid `seq([token_pattern()])` when `token_pattern()` works
   - Trade grammar elegance for simplicity

5. **Test the Full Pipeline Incrementally**
   - Test parsing, extraction, conversion, desugaring separately
   - Then test full pipeline

### Action Items

1. [ ] Add unit tests for ALL `extract_*` functions
2. [ ] Document grammar structure for all rules
3. [ ] Add linting for `ref()` to non-existent rules
4. [ ] Create grammar structure inspector tool
5. [ ] Add integration tests for all pattern types
6. [ ] Create test-driven development checklist

---

## Related Documents

- **[docs/plans/core/18-exhaustiveness-wildcard-bug.md](./18-exhaustiveness-wildcard-bug.md)** - Bug summary
- **[docs/plans/core/19-wildcard-pattern-comprehensive-analysis.md](./19-wildcard-pattern-comprehensive-analysis.md)** - Previous analysis
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core exhaustiveness checking
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Grammar and pattern extraction
