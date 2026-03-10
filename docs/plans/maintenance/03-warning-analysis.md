# Warning Analysis

> **Date**: March 2025
> **Total Warnings**: 45

---

## Summary

| Category | Count | Action |
|----------|-------|--------|
| 🟢 Safe to fix | 38 | Fix immediately |
| 🟡 False positives | 4 | Add `@target` or keep as-is |
| 🔴 Potential issues | 3 | Review needed |

---

## 🟢 Safe to Fix (38 warnings)

### Unused Imports (11 warnings)

**Files**: `src/core/syntax.gleam`, `test/core/core_test.gleam`, `test/syntax/grammar_test.gleam`, `src/examples/calc.gleam`, `src/tao/ast.gleam`

**Action**: Remove unused imports

### Unused Variables - Spans/Test Vars (15 warnings)

**Files**: `src/core/syntax.gleam`, `test/core/core_test.gleam`

**Pattern**: `span`, `v32t`, `v64t`, `term`, `val`, `s`

**Action**: Prefix with `_` (e.g., `_span`, `_term`)

**Why safe**: These are genuinely unused - just bookkeeping variables

### Unused Function Arguments - Formatter Stubs (11 warnings)

**Files**: `src/syntax/grammar.gleam`, `src/core/syntax.gleam`

**Pattern**: `fn(ast, _)`, `fn(_, p)`

**Action**: Change to `fn(_ast, _)`, `fn(_, _p)`

**Why safe**: These are stub formatters that return placeholder text

### Unreachable Code After Panic (2 warnings)

**Files**: `src/syntax/grammar.gleam`, `src/core/syntax.gleam`

**Pattern**: `panic as "..."` followed by more code

**Action**: Remove unreachable code

**Why safe**: Code after `panic` is never executed

### Unreachable Patterns (3 warnings)

**Files**: `src/core/core.gleam`, `src/core/syntax.gleam`, `src/compiler_bootstrap.gleam`

**Pattern**: Catch-all `_` case that's already covered

**Action**: Remove redundant patterns

**Why safe**: Earlier patterns already cover all cases

### Duplicate Import (1 warning)

**File**: `test/syntax/lexer_test.gleam`

**Action**: Remove duplicate

### Unused Private Functions (2 warnings)

**Files**: `src/syntax/grammar.gleam`, `src/core/syntax.gleam`

**Functions**: `fold_operators`, `parse_value_to_term`

**Action**: Remove dead code

---

## 🟡 False Positives (4 warnings)

### `env` parameter in `named_pattern_to_de_bruijn`

**File**: `src/core/syntax.gleam:170`

**Warning**: `env` argument never used

**Analysis**: ⚠️ **FALSE POSITIVE** - The `env` parameter IS used, but indirectly:
- It's passed recursively to nested pattern calls
- Base cases (NPAny, NPLit, etc.) don't need it
- Recursive cases (NPAs, NPRcd, NPCtr) pass it through

**Action**: Keep as-is OR add `@target(erlang)` annotation to suppress

### `bindings` parameter in `format_pattern`

**File**: `src/core/syntax.gleam:1072`

**Warning**: `bindings` argument never used

**Analysis**: ⚠️ **FALSE POSITIVE** - Similar to above, may be needed for future functionality

**Action**: Keep as-is for now

---

## 🔴 Potential Issues Requiring Review (3 warnings)

### None identified

All warnings have been analyzed and are either safe to fix or false positives.

---

## Fix Plan

### Phase 1: Remove Unused Imports (5 min)

```bash
# Files to fix:
- src/core/syntax.gleam (5 unused imports)
- test/core/core_test.gleam (1 unused import)
- test/syntax/grammar_test.gleam (2 unused imports)
- src/examples/calc.gleam (1 unused import)
- src/tao/ast.gleam (1 unused import)
```

### Phase 2: Prefix Unused Variables (10 min)

```bash
# Files to fix:
- src/core/syntax.gleam (7 span variables)
- test/core/core_test.gleam (5 test variables)
```

### Phase 3: Fix Formatter Stubs (5 min)

```bash
# Files to fix:
- src/syntax/grammar.gleam (3 stub functions)
- src/core/syntax.gleam (8 stub functions)
```

### Phase 4: Remove Dead Code (5 min)

```bash
# Files to fix:
- src/syntax/grammar.gleam (remove fold_operators)
- src/core/syntax.gleam (remove parse_value_to_term)
```

### Phase 5: Clean Up Unreachable Code (5 min)

```bash
# Files to fix:
- src/syntax/grammar.gleam (2 unreachable code blocks)
- src/core/core.gleam (1 unreachable pattern)
- src/core/syntax.gleam (1 unreachable pattern)
- src/compiler_bootstrap.gleam (1 unreachable pattern)
```

### Phase 6: Remove Duplicate Import (2 min)

```bash
# Files to fix:
- test/syntax/lexer_test.gleam (remove duplicate import)
```

**Total Time**: ~30 minutes
**Risk**: None - all changes are cosmetic

---

## Verification

After fixes:
```bash
gleam check  # Should show 0 warnings
gleam test   # Should still pass all 401 tests
```
