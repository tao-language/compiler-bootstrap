# Analysis of Remaining 5 Test Failures

**Date**: April 5, 2026
**Status**: 439 passed, 5 failures (unchanged)

---

## Summary of Failing Tests

| Test | Error | Root Cause |
|------|-------|------------|
| `lib_prelude_bool_module_test` | TypeMismatch + NotAFunction | Multi-function cross-reference type mismatch |
| `match_different_result_types_test` | AssertionError | Same root cause |
| `three_match_expressions_no_conflict_test` | AssertionError | Same root cause |
| `match_different_types_test` | AssertionError | Same root cause |
| `local_option_shadows_prelude_test` | ParseError | TypeDecl grammar doesn't support type params |

---

## Detailed Analysis

### Issue 1: Multi-function Cross-Reference Type Mismatch

**Affected Tests**: 4 (all match/multi-function related)

**Exact Error** (from `lib_prelude_bool_module_test`):
```
TypeMismatch(
  VPi([], "_", [VNeut(HVar(4), [EApp(VNeut(HVar(4), [])), EApp(VNeut(HVar(5), []))]),
                VNeut(HVar(3), []), VNeut(HVar(2), []), VNeut(HVar(1), []),
                VNeut(HVar(0), [])],
      VCtrValue(VCtr("Bool", VUnit)),
      Hole(0, Span("lib/prelude/bool.tao", 0, 0, 0, 0))),
  VCtrValue(VCtr("Bool", VUnit)),
  Span("", 0, 0, 0, 0),
  Span("lib/prelude/bool.tao", 36, 17, 36, 20)
)
NotAFunction(Var(4, Span("lib/prelude/bool.tao", 36, 7, 36, 9)),
             VCtrValue(VCtr("Bool", VUnit)))
```

**Interpretation**:
- `Var(4)` at position (line 36, col 7-9) = `or` in `and(or(a, b), not(and(a, b)))`
- Expected: `Bool -> Bool -> Bool` (function type)
- Actual: `Bool` (constructor value)
- The `TypeMismatch` shows a VPi (function type) being compared with Bool
- The VPi's env has HVar(4), HVar(3), HVar(2), HVar(1), HVar(0) — 5 entries

**Root Cause Hypothesis**: When checking the `xor` function body against its annotation type, the annotation type's expected return type (`Bool`) is being used as the expected type for the match expression, instead of the full function type (`Bool -> Bool -> Bool`). This causes Var(4) = `or` to be typed as `Bool` instead of `Bool -> Bool -> Bool`.

**Attempted Fix**: Modified `check` for Fix to detect annotated bodies and use the annotation type for `def_var` instead of `expected_ty`. This did NOT resolve the issue — still 5 failures.

**Why the Fix Didn't Work**: The problem is deeper. The `check_ctr_def` function processes module-level definitions sequentially. Each function's body is checked against its annotation type. But when functions reference each other, the earlier function's type in the environment might not be the full function type. The desugarer creates nested Fix/App structures for sequential function definitions, and the `check` function's handling of these nested structures might be stripping away the function type's domain.

**Next Investigation Step**: The key is in `check_ctr_def` and how it processes sequential function definitions. The error position (36, 17-20) = column 17-20 on line 36 of bool.tao. Looking at the file, line 36 is likely inside the `or` function body where `b` is referenced. This suggests the match's result type is being unified with something it shouldn't be.

### Attempted Fixes (Did Not Resolve)

1. **Annotated Fix handling in `check`**: Modified to use annotation type for `def_var` instead of expected_ty. Still 5 failures.
2. **Debug logging in test_api**: Removed — too complex without proper runtime output.

### What Needs Further Investigation

The exact flow of types through:
1. `check_ctr_def` → sequential function processing
2. `check(Fix(Ann(...)))` → how annotation type is used
3. `infer_match` → how motive result type relates to function return type
4. The VPi env's HVar indices vs the current vars list during type-checking

### Issue 2: TypeDecl Grammar Doesn't Support Type Parameters

**Affected Test**: local_option_shadows_prelude_test

**Symptom**:
```
ParseError(Span("input", 1, 2, 1, 5), "end of input", "type", ...)
```

**Root Cause**: The TypeDecl grammar rule uses `TIdent` for the type name. So `type Option = Some(a) | None` works, but `type Option(a) = Some(a) | None` fails because `(a)` after the type name is not consumed.

**Location**: `src/tao/syntax.gleam` — `type_decl` rule

**Fix needed**: Update TypeDecl grammar to support optional type parameters:
```
type_decl:
  "type" TIdent "(" TIdent ")" "=" (constructor "|")+ ";"
  | "type" TIdent "=" (constructor "|")+ ";"
```

---

## Approaches Considered for Issue 1

### Approach A: Runtime debug logging in type-checker
- **Pros**: Directly reveals wrong unification
- **Cons**: Requires modifying core type-checker, careful output
- **Status**: Attempted but too complex without proper infrastructure

### Approach B: Fix annotation type evaluation for Fix
- **Pros**: Addresses potential stale HVar indices
- **Cons**: Attempted — didn't resolve the issue
- **Status**: Partial fix applied, needs more investigation

### Approach C: Trace check_ctr_def sequential processing
- **Pros**: Likely root cause — how function types accumulate in env
- **Cons**: Complex, requires understanding nested Fix/App structure
- **Status**: Next step for investigation

### Approach D: Shift HVar values in annotation types
- **Pros**: Fixes stale HVar indices
- **Cons**: Complex, error-prone, might break other things

### Approach E: Avoid duplicate name entries in env
- **Pros**: Simpler env structure
- **Cons**: Would require changing both desugarer AND type-checker

**Current Recommendation**: Investigate `check_ctr_def` sequential processing (Approach C) with targeted runtime output.
