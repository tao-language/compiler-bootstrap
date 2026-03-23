# Exhaustiveness Checking Bug: Wildcard Pattern Not Recognized

> **Status**: 🐛 Root Cause Identified
> **Date**: March 2026 (Updated)
> **Severity**: High - prevents wildcard patterns from working
> **Test Status**: 520/522 tests passing (99.6%)
> **See Also**: [docs/plans/core/19-wildcard-pattern-comprehensive-analysis.md](./19-wildcard-pattern-comprehensive-analysis.md)

---

## Problem Description

Wildcard patterns (`_`) in match expressions are not being recognized as exhaustive, even though they should cover all cases.

**Example**:
```tao
let x = 100
match x {
  | _ -> 100  // Error: Pattern match not exhaustive
}
```

**Expected**: No error (wildcard covers all cases)
**Actual**: `error[E0202]: Pattern match not exhaustive`

**Workaround**: Use a variable pattern instead: `| n -> 100`

---

## Root Cause (IDENTIFIED)

**The bug is in the pattern extraction logic** in `extract_single_clause_from_list` (`src/tao/syntax.gleam`).

### What's Working ✅

1. **Grammar Rules**: Correctly parse `_` as `Var("_", span)`
2. **pattern_ast_to_pattern**: Correctly converts `Var("_", span)` → `PWild(span)`
3. **pattern_to_ast**: Correctly converts `PWild(span)` → `AstPAny(span)`
4. **tao_pattern_to_core_pattern**: Correctly converts `AstPAny(span)` → `PAny`
5. **check_exhaustiveness**: Correctly recognizes `PAny` as exhaustive (proven by unit tests)

### What's Broken ❌

**`extract_single_clause_from_list`** doesn't correctly extract the pattern from the grammar structure, returning `PWild(Span("error", ...))` instead of the actual pattern.

```gleam
let pattern = case pattern_items {
  [AstValue(expr)] -> pattern_ast_to_pattern(expr)
  [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
  _ -> PWild(Span("error", 0, 0, 0, 0))  // ❌ This fallback is hit for wildcards
}
```

### Why Variable Patterns Work

Variable patterns (`| n -> ...`) may have a slightly different grammar structure that happens to match the extraction cases, while wildcard patterns (`| _ -> ...`) have a structure that doesn't match, triggering the error fallback.

---

## Pipeline Analysis

| Stage | Component | Status | Notes |
|-------|-----------|--------|-------|
| 1. Grammar | `src/tao/syntax.gleam` | ✅ Working | Parses `_` correctly |
| 2. Pattern Extraction | `extract_single_clause_from_list` | ❌ Broken | Returns error pattern |
| 3. AST Conversion | `pattern_to_ast` | ✅ Working | Converts correctly |
| 4. Desugaring | `tao_pattern_to_core_pattern` | ✅ Working | Converts correctly |
| 5. Exhaustiveness | `check_exhaustiveness` | ✅ Working | Recognizes `PAny` |

---

## Fix Plan

### Immediate Fix: Improve Pattern Extraction

See `docs/plans/core/19-wildcard-pattern-comprehensive-analysis.md` for detailed fix plan.

### Debug Step: Add Logging

Add debug output to see the actual grammar structure being produced for wildcards vs variables.

---

## Implementation Status

- [x] Added tests to reproduce the issue
- [x] Identified pattern extraction issue
- [x] Confirmed Core exhaustiveness checking works correctly
- [x] Confirmed desugaring works correctly
- [x] Confirmed AST conversion works correctly
- [x] Created comprehensive analysis document
- [ ] Add debug logging to identify exact grammar structure
- [ ] Fix pattern extraction to handle all structures
- [ ] Verify fix works for all pattern types

---

## Related Documents

- **[docs/plans/core/19-wildcard-pattern-comprehensive-analysis.md](./19-wildcard-pattern-comprehensive-analysis.md)** - Comprehensive analysis with pipeline breakdown
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language implementation
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Tao syntax (pattern parsing)
- **[src/tao/desugar.gleam](../../src/tao/desugar.gleam)** - Tao desugarer
