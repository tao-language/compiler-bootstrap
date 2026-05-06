# Test Failure Analysis (Updated 2026-05-05)

> **Date:** 2026-05-05
> **Status:** 937 tests passing, 3 failures remaining

## Overview

Three tour example tests are failing. Debugging has revealed that:
1. **All 3 failures are evaluation bugs, NOT parser bugs** — Parsing produces valid terms
2. **The root cause is in how `$type` inside `$let` evaluates** — produces unexpected values
3. **FFI untyped argument handling was fixed** — but tour files still fail

## Current Test Results

```
937 passed, 3 failures
```

### Failing Tests

| Test | Expected | Actual | Category |
|------|----------|--------|----------|
| `t04_type_definitions_04_gadt_expr_test` | `VLit(Int(3))` | `VErr` | GADT expr with FFI calls |
| `t05_pattern_matching_10_exhaustiveness_test` | `VLit(Int(42))` | `VRcd([#("", VErr), ...])` | TypeDef + Match |
| `t07_advanced_01_default_values_test` | `VLit(LitInt(0))` | `VErr` | Record type defaults |

## Debugging Results

### What Works
- ✅ Standalone `$match` parses and evaluates correctly
- ✅ Standalone `$let` + `$type` parses correctly (produces Ann/App/Lam)
- ✅ `parse_typed_arg_list_acc` now handles untyped FFI arguments
- ✅ All 937 unit tests pass

### What Doesn't Work
- ❌ `$let` + `$type` + `$match` combination evaluates to wrong value
- ❌ The `$let` binding doesn't produce `VTypeDef` when evaluated
- ❌ The tour file tests fail because evaluation produces unexpected values

### Root Cause Analysis

The issue is in the evaluation of `$let` bindings when the value is a `$type` definition:

1. **Parsing:** `$let Option = $type<...> {...}` produces `App(Lam(...), TypeDef(...))` ✓
2. **Evaluation:** `App(Lam(...), TypeDef(...))` should evaluate to `VTypeDef(...)` ✗
3. **Actual result:** Something other than `VTypeDef` (investigation shows it's not `VErr` or `VTypeDef`)

The parser is correct. The evaluation is producing a valid value, but it's not the expected `VTypeDef`.

## Fix Strategy

### Priority 1: Fix `$type` evaluation inside `$let`

The `$type` inside `$let` needs to evaluate to `VTypeDef`. The current flow is:
1. `parse_type_def` produces `TypeDef` term
2. `parse_let` wraps it in `let_var` → `App(Lam(...), TypeDef(...))`
3. `evaluate` should produce `VTypeDef(...)`

Need to trace through `evaluate` to find where the value goes wrong.

### Priority 2: Fix tour file tests after root cause fix

Once the `$type` evaluation is fixed, the tour file tests should pass:
- `t04_gadt_expr_test` - GADT expr with FFI calls
- `t05_exhaustiveness_test` - TypeDef + Match
- `t07_default_values_test` - Record type defaults

### Priority 3: Additional test quality improvements

- Fix weak assertions in remaining test files
- Consolidate lexer test files
- Fix remaining compiler warnings

## Implementation Plan

### Phase 1: Debug evaluation flow (Current)
1. ✅ Added debug tests to isolate the issue
2. ✅ Confirmed parsing is correct
3. ✅ Confirmed standalone `$match` evaluates correctly
4. ✅ Confirmed standalone `$let` + `$type` parses correctly
5. ⏳ Need to trace `evaluate` to find where `VTypeDef` is lost

### Phase 2: Fix evaluation bug
1. Add targeted unit test for `$type` evaluation
2. Trace through `evaluate` function
3. Fix the evaluation logic
4. Verify all tour file tests pass

### Phase 3: Test quality improvements
1. Fix weak assertions in `test/core/syntax_test.gleam`
2. Fix weak assertions in `test/core/generalize_test.gleam`
3. Fix weak assertions in `test/core/infer_test.gleam`
4. Consolidate `test/syntax/base_lexer_test_new.gleam` into `base_lexer_test.gleam`
5. Consolidate `test/core/type_defs_test.gleam` into `ast_test.gleam`

## Expected Outcome

After Phase 2: 940+ tests passing, 0 failures
After Phase 3: 940+ tests passing, 0 failures, improved test quality
