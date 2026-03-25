# Lambda Inference Root Cause Analysis

> **Date**: March 2026
> **Status**: 📋 Root Cause Identified

---

## Root Cause: Domain Not Generalized

The `InfiniteType` error is caused by the **domain type not being generalized** in `infer(Lam)`.

### The Problem

In `infer(Lam)`:
```gleam
let #(generalized_implicit, generalized_t1, generalized_t2) =
  generalize_holes(holes_to_generalize, implicit, t1_hole, body_ty_shifted, ...)
```

- `t1_hole` = hole 4 (outer lambda's parameter type)
- `body_ty_shifted` = inner lambda's type = `VPi([], "b", [], HVar(0), Bool)`
- `holes_to_generalize` = [] (hole 4 not in body_ty!)

When `holes_to_generalize = []`, `generalize_holes` returns:
```gleam
#(existing_implicit, domain, quote(ffi, lvl, codomain, span))
```

So `generalized_t1 = domain = t1_hole = Hole(4)` (NOT generalized!)

The outer lambda's type becomes:
```
VPi([], "a", [], Hole(4), VPi([], "b", [], HVar(0), Bool))
```

### Why This Causes InfiniteType

When the type checker tries to use this type:
1. Hole 4 is unsolved
2. During application, hole 4 should unify with `Bool`
3. But hole 4 appears in the type structure
4. Occurs check fails because hole 4 is in its own "context"

### The Fix

The domain (`t1_hole`) should ALWAYS be generalized, regardless of whether it appears in the body type.

**Option 1**: Always include `t1_hole` in `holes_to_generalize`
```gleam
let holes_to_generalize = [t1_hole_id, ..list.filter(all_holes, fn(id) { id >= holes_before })]
```

**Option 2**: Generalize domain separately
```gleam
let #(generalized_implicit, _, generalized_t2) =
  generalize_holes(holes_to_generalize, implicit, t1_hole, body_ty_shifted, ...)
let generalized_t1 = HVar(list.length(implicit))  // First new implicit param
```

**Option 3**: Modify `generalize_holes` to always generalize the domain
```gleam
fn generalize_holes(..., domain: Value, ...) {
  // Always substitute holes in domain
  let generalized_domain = subst_value_with_hole_vars(hole_subst, domain)
  // ...
}
```

### Recommended Fix: Option 1

Always include `t1_hole` in `holes_to_generalize` because:
1. The domain is ALWAYS a hole created for this lambda
2. The hole should ALWAYS be generalized to an implicit param
3. This matches the semantics of lambda abstraction

```gleam
// Filter to only holes created during this lambda's inference
let holes_to_generalize = list.filter(all_holes, fn(id) { id >= holes_before })

// ALWAYS include t1_hole in holes_to_generalize
// The domain hole should always be generalized to an implicit param
let t1_hole_id = case t1_hole {
  VNeut(HHole(id), []) -> id
  _ -> holes_before  // Should not happen
}
let holes_to_generalize = case list.contains(holes_to_generalize, t1_hole_id) {
  True -> holes_to_generalize
  False -> [t1_hole_id, ..holes_to_generalize]
}
```

---

## Test Plan

1. Apply the fix
2. Test with prelude bool module
3. Test with nested lambdas
4. Verify all existing tests pass

---

## Related Documents

- **[23-lambda-inference-de-bruijn-fix.md](23-lambda-inference-de-bruijn-fix.md)** - Previous attempt
- **[22-lambda-inference-fix-attempt-2.md](22-lambda-inference-fix-attempt-2.md)** - Attempt 2
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Final analysis
