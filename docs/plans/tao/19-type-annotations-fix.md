# Type Annotations and Constructor Registration Fix

> **Goal**: Properly desugar type annotations and register type definitions in Core
> **Status**: 🚧 **In Progress** - Phase 1-3 complete, Phase 4 requires further investigation
> **Date**: March 2026
> **Priority**: **CRITICAL** - Affects ALL code, not just prelude

---

## Overview

**Problem**: The Tao compiler currently has issues with type annotations in function definitions due to hole generalization not properly substituting holes in nested lambda types.

**Impact**: 
- Type annotations like `fn not(b: Bool) -> Bool` cause InfiniteType errors
- 5 test failures remain (lib_prelude_bool, nested_fn, higher_order, recursive_fn, pattern_mismatch)

**Root Cause**: Lambda inference creates holes for parameter types, but hole generalization doesn't properly substitute holes in nested lambda types. The `generalize_holes` function was quoting the body type before substitution, so nested lambda types (stored as `Value`) weren't being updated.

**Solution**: 
1. Modified `generalize_holes` to accept `Value` for codomain and substitute before quoting
2. Modified `infer(Lam)` to collect holes from `body_ty` (Value) instead of quoted term
3. Issue persists - requires further investigation

---

## Current Status

### ✅ Phase 1: Type Annotations Infrastructure (COMPLETE)

**Completed**:
- Created `build_core_type_from_ast()` function
- Added `CorePi` constructor for Pi types
- Added `build_fn_type()` for building function types

**Issues**:
- Function type annotations with holes cause InfiniteType errors
- Currently disabled - annotations are parsed but not added

### ✅ Phase 2: Constructor Registration (COMPLETE)

**Completed**:
- Modified `process_type_definitions()` to register type constructors
- Created `state_with_constructors()` to merge constructor environments
- Updated `test_api.gleam` to use constructor environment

**Result**: Type constructors like `Bool`, `Option`, `Result` are properly registered.

### ✅ Phase 3: Type Checker Fixes (COMPLETE)

**Completed**:
- Modified `check(Fix)` to use expected type directly
- Modified `check(Lam)` to use domain type from expected VPi
- Fixed `infer(Ann)` to use `eval` for annotation types

**Issues**:
- These fixes help but don't solve the root cause
- Lambda inference still creates holes that aren't properly solved

### 🚧 Phase 4: Lambda Inference Fix (IN PROGRESS)

**Completed**:
- Modified `generalize_holes` to accept `Value` for codomain
- Modified `infer(Lam)` to collect holes from `body_ty` (Value)

**Issues**:
- Hole substitution still not working correctly
- `HHole(4)` remains in nested lambda types after generalization
- Requires further investigation with debug output

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType error persists |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch) |
| `tao examples` | ⚠️ MIXED | 3 failures |
| **Total** | **519 passed, 5 failures** | Same as baseline |

---

## Related Documents

- **[20-type-annotations-root-cause.md](20-type-annotations-root-cause.md)** - Root cause analysis
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Previous analysis
- **[22-lambda-inference-fix-attempt-2.md](22-lambda-inference-fix-attempt-2.md)** - Attempt 2 analysis
- **[../core/core.gleam](../../src/core/core.gleam)** - Core type checker
- **[../desugar.gleam](../../src/tao/desugar.gleam)** - Desugaring logic

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial plan created |
| March 2026 | Phase 1-3 implemented |
| March 2026 | Root cause identified: hole generalization issue |
| March 2026 | Attempt 2: generalize_holes fix (partial) |
| March 2026 | Issue persists - requires further investigation |
