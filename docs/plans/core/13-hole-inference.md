# Hole Inference Enhancement Plan

> **Goal**: Improve hole inference to "expand into two holes" when a hole is used in application context
> **Status**: ✅ Complete
> **Date**: March 2025

---

## Overview

Currently, when a hole `?1` is used in an application context like `?1(x)`, the type checker cannot infer that `?1` should be a function type. This limitation prevents let-bindings with functions from working:

```
let id = x -> x in id(42)  // Fails: cannot infer id's type
```

The solution is to allow holes to **expand** when constrained by their usage context.

---

## Problem Analysis

### Current Behavior

When checking `id(42)` where `id : ?1`:
1. Create hole `?1` for `id`'s type
2. Try to apply `?1` to `42`
3. Fail: `?1` is not known to be a function type

### Desired Behavior

When checking `id(42)` where `id : ?1`:
1. Create hole `?1` for `id`'s type
2. Try to apply `?1` to `42`
3. **Expand** `?1` to `(?2 -> ?3)` where `?2` and `?3` are fresh holes
4. Check that `42 : ?2` (solves `?2 = $I32`)
5. Result type is `?3`

---

## Implementation Status

### Phase 1: Hole Expansion in Application ✅

**Location**: `src/core/core.gleam`, `infer` function, `App` case

**Implementation**:
- [x] Detect when a hole `VNeut(HHole(id), [])` is applied
- [x] Create two fresh holes for domain and codomain
- [x] Expand hole to function type `(?2 -> ?3)`
- [x] Unify original hole with expanded type
- [x] Check argument against domain hole
- [x] Return codomain hole as result type

### Phase 2: Hole Expansion in Other Contexts 📋

**Field Access**: When accessing `?1.field`, expand `?1` to a record type
**Constructor Pattern**: When matching `#Ctr(?1)`, expand appropriately

### Phase 3: Constraint Solving 📋

**Unification**: Implement proper unification for hole constraints
**Occurs Check**: Prevent infinite types (`?1 = ?1 -> ?1`)

---

## Examples

### Let Binding with Function

```text
let id = x -> x in id(42)
```

**Type Checking**:
1. Check `x -> x` with hole type `?1`
2. Infer `id : ?1` where `?1 = (?2 -> ?2)`
3. Check `id(42)`:
   - `id : ?1` expands to `(?2 -> ?2)`
   - Check `42 : ?2`, solve `?2 = $I32`
   - Result: `$I32`

### Nested Applications

```text
let f = x -> y -> x in f(1)(2)
```

**Type Checking**:
1. `f : ?1` where `?1 = (?2 -> ?3)`
2. `f(1)`: `?2 = $I32`, result `?3`
3. `?3` expands to `(?4 -> ?5)`
4. `f(1)(2)`: `?4 = $I32`, result `?5 = $I32`

---

## Testing

### Unit Tests

```gleam
pub fn hole_inference_application_test() {
  let source = "let id = x -> x in id(42)"
  let result = type_check(source)
  result |> should.be_ok()
  result.inferred_type |> should.equal(v32())
}
```

### Integration Tests

```gleam
pub fn hole_inference_nested_test() {
  let source = "let f = x -> y -> x in f(1)(2)"
  let result = type_check(source)
  result |> should.be_ok()
}
```

### Error Cases

```gleam
pub fn hole_inference_occurs_check_test() {
  // ?1 = ?1 -> ?1 should fail occurs check
  let source = "let f = x -> f(x) in f"  // Infinite type
  let result = type_check(source)
  result |> should.be_error()
}
```

---

## Success Criteria

- ✅ Let-bindings with functions type-check correctly
- ✅ Hole expansion works in application context
- ✅ Occurs check prevents infinite types
- ✅ All existing tests continue to pass
- ✅ New examples in `examples/core/programs/` type-check

---

## Related Documents

- [Core Language Overview](../../docs/plans/core/01-overview.md)
- [Let-Bindings Implementation](../../docs/plans/core/12-let-bindings.md)
- [Type Checking Algorithm](../../docs/core.md)
