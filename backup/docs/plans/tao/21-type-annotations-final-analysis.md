# Type Annotations Fix - Final Analysis

> **Date**: March 2026
> **Status**: 📋 Analysis Complete

---

## Root Cause Summary

The InfiniteType error occurs due to a fundamental mismatch between how holes are created during **desugaring** vs. **type checking**:

### The Problem

1. **Desugaring creates holes with fixed IDs**: `CoreHole(0, span)` always uses ID 0
2. **Type checking creates holes with unique IDs**: `new_hole()` uses `s.hole` counter
3. **When both are used together, conflicts occur**:
   - Desugaring holes become `VNeut(HHole(0), [])` after evaluation
   - Type checking holes become `VNeut(HHole(4), [])`, `VNeut(HHole(5), [])`, etc.
   - During unification, the occurs check finds conflicts

### The Error Flow

```
fn xor(a: Bool, b: Bool) -> Bool {
  and(or(a, b), not(and(a, b)))
}
```

1. `infer(Fix)` creates `Hole(3)` for `xor`'s result type
2. `infer(Lam)` for parameter `a` creates `Hole(4)` for domain
3. `infer(Lam)` for parameter `b` creates `Hole(5)` for domain  
4. Body is inferred, creating more holes for function applications
5. Holes are generalized to `HVar(0)`, `HVar(1)` (implicit type variables)
6. But some holes (like `Hole(4)`) remain in the type
7. During unification, occurs check finds `Hole(4)` in a type containing `HVar(0)`, `HVar(1)`
8. **InfiniteType error**: hole appears in its own type

### Why This Happens

The type checker's lambda inference:
1. Creates a hole for each parameter's type
2. Infers the body type (which may contain more holes)
3. Generalizes holes to implicit type variables (HVar)
4. But holes that appear in the body are NOT always generalized

When the body contains function applications, the function's type (with its own holes) is used. These holes may not be generalized, leading to the InfiniteType error.

---

## Solution: Don't Use Holes in Annotations

The fix is to **not create holes during desugaring**. Instead:

1. **Don't annotate function types** - let the type checker infer them
2. **Use constructor environment** for known types (Bool, Option, etc.)
3. **Rely on check(Fix) and check(Lam)** fixes for recursive functions

### Changes Made

1. **Removed function type annotations** from `StmtFn` handling
2. **Kept constructor registration** in `process_type_definitions`
3. **Kept state_with_constructors** to merge constructor environments
4. **Kept check(Fix) and check(Lam)** fixes for when expected types are available

### What Works

- Type definitions are properly registered (`Bool`, `True`, `False`)
- Constructor environment is available during type checking
- Recursive functions work when types can be inferred

### What Doesn't Work

- Functions with type annotations still cause InfiniteType errors
- The type checker creates holes for parameter types that aren't properly solved
- Lambda inference generalizes some holes but not all

---

## Next Steps

### Immediate (Required)

1. **Fix lambda inference** to properly solve all holes
2. **Ensure occurs check** doesn't fail for valid recursive definitions
3. **Test with prelude** to verify bool module works

### Medium Term

1. **Add proper Pi type support** for function type annotations
2. **Create fresh holes during type checking** instead of desugaring
3. **Add tests** for type annotations with various parameter combinations

### Long Term

1. **Support dependent types** fully with proper hole management
2. **Optimize type inference** to minimize hole creation
3. **Add type-directed desugaring** for better error messages

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType error in `xor` function |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch - unrelated) |
| `tao examples` | ⚠️ MIXED | 3 failures (nested_fn, higher_order, recursive_fn) |
| **Total** | **520 passed, 4 failures** | Same as before fixes |

---

## Files Changed

- `src/core/core.gleam` - check(Fix) and check(Lam) fixes
- `src/tao/desugar.gleam` - Removed function type annotations, added CorePi
- `src/tao/test_api.gleam` - state_with_constructors
- `docs/plans/tao/20-type-annotations-root-cause.md` - This analysis

---

## Key Insight

**Holes should only be created by the type checker**, not during desugaring. The type checker's `new_hole()` function properly manages hole IDs and ensures uniqueness. Desugaring should use other mechanisms (like constructor environment) to provide type information.
