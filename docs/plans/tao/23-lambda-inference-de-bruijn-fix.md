# Lambda Inference Fix - De Bruijn Index Issue

> **Date**: March 2026
> **Status**: 📋 Root Cause Identified

---

## Root Cause: De Bruijn Index Mismatch

The `InfiniteType` error is caused by **De Bruijn index mismatch** when generalizing nested lambdas.

### The Problem

When the inner lambda generalizes its holes:
1. Inner lambda creates hole 5 for parameter `b`'s type
2. Inner lambda generalizes: hole 5 → HVar(0)
3. Inner lambda's type: `VPi([], "_", [], HVar(0), Bool)`

When the outer lambda uses this type:
1. Outer lambda receives `body_ty = VPi([], "_", [], HVar(0), Bool)`
2. Outer lambda generalizes its own holes
3. Outer lambda's type: `VPi([], "_", [], HVar(0), VPi([], "_", [], HVar(0), Bool))`

**Problem**: The inner `VPi`'s `HVar(0)` now refers to the outer lambda's first implicit param, not the inner lambda's!

### Why This Causes InfiniteType

When the type checker tries to unify types:
1. Outer lambda's type has `HVar(0)` for both outer and inner params
2. During application, both params get the same type
3. This creates a circular dependency
4. Occurs check fails with `InfiniteType`

### The Fix

When the outer lambda receives a nested lambda's type, it should **shift the HVar indices** by the number of new implicit params the outer lambda adds.

For example:
- Inner lambda's type: `VPi([], "_", [], HVar(0), Bool)` (HVar(0) is inner's first implicit)
- Outer lambda adds 1 implicit param
- Shifted type: `VPi([], "_", [], HVar(1), Bool)` (HVar(1) is inner's first implicit in outer's context)

### Implementation

Add a function to shift HVar indices in a Value:

```gleam
/// Shift HVar indices in a Value by a given offset.
/// Used when embedding a nested lambda's type in an outer context.
fn shift_hvar_in_value(value: Value, offset: Int) -> Value {
  case value {
    VNeut(HVar(level), []) -> VNeut(HVar(level + offset), [])
    VNeut(HVar(level), spine) -> VNeut(HVar(level + offset), list.map(spine, shift_hvar_in_elim(offset, _)))
    VPi(implicit, name, env, in_val, out_term) ->
      VPi(implicit, name, env, shift_hvar_in_value(in_val, offset), shift_hvar_in_term(out_term, offset))
    VLam(implicit, name, env, body) ->
      VLam(implicit, name, list.map(env, shift_hvar_in_value(_, offset)), shift_hvar_in_term(body, offset))
    // ... handle other cases
    _ -> value
  }
}
```

Then in `infer(Lam)`, shift the body_ty before using it:

```gleam
let #(body_val, body_ty, s) = infer(s, body)

// Shift HVar indices in body_ty by the number of new implicit params
let num_new_implicit = list.length(holes_to_generalize)
let body_ty_shifted = shift_hvar_in_value(body_ty, num_new_implicit)

// Use body_ty_shifted for generalization
let #(generalized_implicit, generalized_t1, generalized_t2) =
  generalize_holes(holes_to_generalize, implicit, t1_hole, body_ty_shifted, s, s.ffi, list.length(env), span)
```

---

## Test Plan

1. Add unit test for `shift_hvar_in_value`
2. Test with nested lambdas: `fn(a) { fn(b) { a } }`
3. Test with prelude bool module
4. Verify all existing tests pass

---

## Related Documents

- **[22-lambda-inference-fix-attempt-2.md](22-lambda-inference-fix-attempt-2.md)** - Previous attempt
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Final analysis
