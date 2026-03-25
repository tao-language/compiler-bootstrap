# Type Annotations Fix - Root Cause Analysis

> **Date**: March 2026
> **Status**: 📋 Analysis Complete, Fix In Progress

---

## Root Cause Analysis

### The Problem

When building function type annotations with `CoreHole(0, span)` for unannotated parameter types, all holes share the **same fixed ID** (0). During type checking:

1. `infer(Ann(Fix(name, lam), Pi(Hole(0), Hole(1), Bool)))` is called
2. `eval()` converts `Hole(0)` and `Hole(1)` to `VNeut(HHole(0), [])` and `VNeut(HHole(1), [])`
3. These become the domain types in the expected `VPi` type
4. When checking the lambda body, new holes are created via `new_hole()` (e.g., `HHole(4)`)
5. The occurs check fails because the annotation holes (`HHole(0)`, `HHole(1)`) appear in the expected type, while inference creates different holes (`HHole(4)`, etc.)
6. Unification tries to unify `HHole(4)` with a type containing `HHole(0)`, causing InfiniteType error

### Why Fixed Hole IDs Are Wrong

The type checker's `new_hole()` function creates **unique** holes:

```gleam
fn new_hole(s: State) -> #(Value, State) {
  let hole = VNeut(HHole(s.hole), [])  // Uses s.hole (unique counter)
  #(hole, State(..s, hole: s.hole + 1))  // Increments counter
}
```

But desugaring creates holes with **fixed IDs**:

```gleam
// In build_core_type_from_ast:
None => #(CoreHole(0, span), dc)  // Always ID 0!
```

This means:
- All unannotated parameters get the same hole ID
- These holes are created **before** type checking starts
- The type checker's hole counter doesn't know about them
- Unification fails because holes aren't properly tracked

### The Error

```
InfiniteType(4, VPi([], "_", 
  [VNeut(HVar(1), []), VNeut(HVar(0), [])],  <- Holes from annotation
  VPi([], "_", 
    [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
    VNeut(HHole(4), []),  <- Hole from inference
    Hole(5, ...)
  ), 
  Hole(3, ...)
))
```

The error shows:
- `HVar(1)` and `HVar(0)`: Hole variables from the annotation (converted to neutral values)
- `HHole(4)`: Fresh hole created during inference
- The occurs check finds that unifying `HHole(4)` with a type containing `HVar(0)`/`HVar(1)` would create an infinite type

---

## Solution Options

### Option 1: Don't Use Holes in Annotations (RECOMMENDED)

**Approach**: Only annotate with the return type, not the full function type.

```gleam
// Instead of: Ann(Fix(name, lam), Pi(Hole(0), Hole(1), Bool))
// Use: Ann(Fix(name, lam), Bool)
```

**Pros**:
- Simple to implement
- Avoids hole ID problems entirely
- Return type annotation is most useful for error messages

**Cons**:
- Parameter types not enforced by annotation
- Type checker still infers parameter types from context

**Implementation**:
```gleam
let core_fix = case return_type {
  Some(ret_ty_ast) -> {
    let #(core_ret_ty, _) = build_core_type_from_ast(ret_ty_ast, dc1, span)
    let core_fix_untyped = CoreFix(name, core_lam, span)
    CoreAnn(core_fix_untyped, core_ret_ty, span)  // Just return type!
  }
  None -> CoreFix(name, core_lam, span)
}
```

### Option 2: Create Fresh Holes During Type Checking

**Approach**: Use a special marker (e.g., `CoreInfer`) instead of `CoreHole`, and create fresh holes during type checking.

```gleam
// New CoreTerm variant:
CoreInfer(span: Span)  // "Infer this type"

// In type checker:
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term {
    Infer(span) -> {
      let #(hole_val, s) = new_hole(s)  // Fresh hole!
      #(hole_val, hole_val, s)
    }
    // ...
  }
}
```

**Pros**:
- Proper hole management
- Can annotate full function types

**Cons**:
- Requires changes to core/core.gleam
- More complex implementation

### Option 3: Don't Annotate Functions At All

**Approach**: Rely on constructor environment and type inference.

**Pros**:
- Simplest implementation
- No hole management issues

**Cons**:
- Less precise error messages
- Type annotations ignored

---

## Recommended Fix: Option 1

Annotate fixpoints with **return type only**, not full function type. This provides useful type information for error messages while avoiding hole ID problems.

### Changes Required

1. **`src/tao/desugar.gleam`**: Modify `StmtFn` handling to annotate with return type only
2. **`src/core/core.gleam`**: Ensure `infer(Ann)` handles non-Pi type annotations correctly
3. **Remove unused code**: `build_fn_type`, `build_pi_type` (or keep for future use)

### Test Cases

```tao
// Should work: return type annotation
fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}

// Should work: no annotation
fn id(x) {
  x
}

// Should work: recursive function with return type
fn factorial(n: I32) -> I32 {
  if n <= 1 {
    1
  } else {
    n * factorial(n - 1)
  }
}
```

---

## Implementation Plan

### Phase 4A: Return Type Only Annotations

- [ ] Modify `StmtFn` to annotate with return type only
- [ ] Test with prelude bool module
- [ ] Test with recursive functions
- [ ] Verify all existing tests pass

### Phase 4B: Full Function Type Annotations (Future)

- [ ] Add `CoreInfer` variant for "infer this type"
- [ ] Modify `infer(Ann)` to create fresh holes for `CoreInfer`
- [ ] Test with fully annotated functions
- [ ] Test with partially annotated functions

---

## Related Documents

- **[19-type-annotations-fix.md](19-type-annotations-fix.md)** - Main implementation plan
- **[../core/core.gleam](../../src/core/core.gleam)** - Core type checker
- **[../desugar.gleam](../../src/tao/desugar.gleam)** - Desugaring logic
