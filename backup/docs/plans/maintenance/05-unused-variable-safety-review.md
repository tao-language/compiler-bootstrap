# Unused Variable Analysis - Safety Critical Review

> **Date**: March 2025
> **Purpose**: Verify each unused variable is safe to prefix with `_`
> **Status**: ✅ Complete - 20 fixed, 25 remaining (require review or are false positives)

---

## Summary

| Category | Count | Status |
|----------|-------|--------|
| ✅ Fixed (safe) | 20 | Applied |
| ⚠️ False positive | 1 | Keep as-is (`env` parameter) |
| ⚠️ Review needed | 2 | `bindings` parameter, unreachable patterns |
| 🔴 Dead code | 2 | Remove `fold_operators`, `parse_value_to_term` |
| 🔴 Unused imports | 11 | Safe to remove |
| 🔴 Test variables | 5 | Need careful review (some are used!) |
| 🔴 Unreachable code | 3 | After panic - safe to clean |

**Starting warnings**: 45
**Fixed**: 20
**Remaining**: 25

---

## Applied Fixes ✅

### 1. `fresh` → `_fresh` in `src/core/core.gleam:1139`

**Reason**: Only need State side effect, not the Value

**Status**: ✅ Applied

---

### 2-8. `span` → `_span` in `src/core/syntax.gleam:172-187`

**Reason**: Span info discarded in NamedPattern → Pattern conversion

**Status**: ✅ Applied (7 occurrences)

---

### 9-17. `p` → `_p` in formatter stubs `src/core/syntax.gleam:288-296`

**Reason**: Stub formatters don't use parameters

**Status**: ✅ Applied (9 occurrences)

---

### 18-20. `ast` → `_ast` in formatter stubs `src/syntax/grammar.gleam`

**Reason**: Stub formatters don't use parameters

**Status**: ✅ Applied (3 occurrences)

---

## Not Applied - Require Careful Review

### Test Variables (5 occurrences)

**WARNING**: Test variables that appear unused may actually be used in subsequent lines or case expressions.

**Example that BROKE**:
```gleam
let term = call("add", [hole(0, s1), i32(1, s2)], s3)  // term used 2 lines later
let #(val, s) = c.comptime_eval(state, term)  // val used in case, s unused
```

**Action**: Do NOT fix test variables without reading the full test context.

---

## False Positive - DO NOT CHANGE

### `env` parameter in `src/core/syntax.gleam:170`

**Status**: ❌ Keep as-is

**Reason**: Passed recursively to nested pattern calls - essential for De Bruijn conversion.

---

## Remaining Warnings (25)

See `03-warning-analysis.md` for complete list and fix plan.
