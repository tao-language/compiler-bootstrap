# Polymorphic Constructors Implementation

> **Goal**: Enable full type parameter support for prelude constructors (`Option(a)`, `Result(a,e)`)
> **Status**: ⏳ **In Progress** - Type parameters implemented, match type checking needs refinement
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Prelude constructors registered in `initial_state` with type parameters
- ✅ Monomorphic constructors work (`True`, `False`, `LT`, `EQ`, `GT`)
- ✅ Core type system supports type parameters in `CtrDef`
- ✅ Constructor type parameter instantiation in `check_ctr_def`
- ✅ **424 tests passing**

### What's Pending

- 📋 Fix match expression type checking for constructor values
- 📋 Define proper return types for constructors (not just `I32T`)
- 📋 Create working examples with full type checking
- 📋 Add unit tests for polymorphic constructors

### Related

- See **[02-prelude.md](./02-prelude.md)** for prelude specification
- See **[04-import-system.md](./04-import-system.md)** for import system
- See **[../core/02-syntax.md](../core/02-syntax.md)** for Core syntax

---

## Problem Analysis

### Current State

Prelude constructors are registered with simplified types:

```gleam
// Current (simplified - doesn't support polymorphism)
#("Some", CtrDef([], Term(Typ(0), no_span), Term(Typ(1), no_span)))
#("None", CtrDef([], Term(Typ(0), no_span), Term(Typ(1), no_span)))
```

This means:
- `Some` has type `Type(0) -> Type(1)` (takes any type, returns a type)
- But we can't express `Some: (a : Type) -> a -> Option(a)`
- Type parameter `a` is not tracked

### Desired State

```gleam
// Desired (polymorphic)
#("Some", CtrDef(
  ["a"],                              // Type parameter
  Term(Var(0), span),                 // Argument type: a
  Term(App(Var(1), [Var(0)]), span)   // Return type: Option(a)
))
```

This expresses:
- `Some` has type parameter `a`
- Takes argument of type `a`
- Returns `Option(a)` where `Option` is the type constructor

---

## Root Cause

### Issue 1: CtrDef Type Representation

The `CtrDef` type uses `Term` for `arg_ty` and `ret_ty`, but type parameters need special handling:

```gleam
pub type CtrDef {
  CtrDef(
    params: List(String),    // Type parameter names
    arg_ty: Term,            // Argument type (can reference params)
    ret_ty: Term,            // Return type (can reference params)
  )
}
```

When checking constructor application, we need to:
1. Instantiate type parameters with fresh type variables
2. Check argument against instantiated `arg_ty`
3. Return instantiated `ret_ty`

### Issue 2: Constructor Lookup

When looking up a constructor, we need to:
1. Get the `CtrDef` from the constructor environment
2. Instantiate type parameters
3. Return the instantiated type

### Issue 3: Type Checking Constructor Applications

Current code doesn't handle type parameter instantiation:

```gleam
// Current (from check_ctr_def)
fn check_ctr_def(s: State, ctr: CtrDef) -> #(List(Int), Value, Value, State) {
  let #(params, arg_ty, ret_ty) = ctr
  // ... needs to instantiate params with fresh vars
}
```

---

## Implementation Plan

### Phase 1: Fix CtrDef Type Checking

#### Step 1.1: Add Type Parameter Instantiation

Create helper function to instantiate type parameters:

```gleam
/// Instantiate type parameters with fresh type variables
fn instantiate_ctr_params(
  s: State,
  params: List(String),
  ty: Term,
) -> #(List(Int), Term, State) {
  // For each param, create a fresh type variable
  // Substitute Var(i) with the fresh var in ty
}
```

#### Step 1.2: Update `check_ctr_def`

Modify to use instantiation:

```gleam
fn check_ctr_def(s: State, ctr: CtrDef) -> #(List(Int), Value, Value, State) {
  let CtrDef(params, arg_ty, ret_ty) = ctr
  let #(param_vals, arg_ty_inst, s) = instantiate_ctr_params(s, params, arg_ty)
  let #(param_vals, ret_ty_inst, s) = instantiate_ctr_params(s, params, ret_ty)
  // ... continue with instantiated types
}
```

### Phase 2: Fix Prelude Constructor Definitions

#### Step 2.1: Define Type Constructors

First, define `Option`, `Result` as type constructors:

```gleam
// Option: Type -> Type
// Takes a type 'a', returns Option(a)
#("Some", CtrDef(
  ["a"],
  Term(Var(0), no_span),                    // arg: a
  Term(App(Var(1), [Var(0)]), no_span)      // ret: Option(a)
))
```

Wait - this requires `Option` to be defined. We need:
1. A type constructor `Option: Type -> Type`
2. Constructors `Some` and `None` that return `Option(a)`

#### Step 2.2: Simplified Approach

For now, use a simpler representation:

```gleam
// Some: (a : Type) -> a -> Type(0)
// The return type is just Type(0), not Option(a)
// Type checking ensures consistency via pattern matching
#("Some", CtrDef(
  ["a"],
  Term(Var(0), no_span),        // arg: a (the type parameter)
  Term(Typ(0), no_span)         // ret: Type(0) (simplified)
))
```

This is simpler but loses some type information. Full GADT-style types require more work.

### Phase 3: Update Examples

Create working examples:

```core
// Option example
%let x = #Some(I32(42)) in
match(x, [
  (#Some(n), None, n),
  (#None, None, I32(0))
])
```

---

## Technical Details

### Type Parameter Representation

Type parameters are represented as `Var(i)` where `i` is the De Bruijn index:
- `Var(0)` = first type parameter
- `Var(1)` = second type parameter
- etc.

### Instantiation

When using a constructor, we:
1. Create fresh type variables for each parameter
2. Substitute `Var(i)` with the fresh variable
3. Use the instantiated type for checking

Example:
```
Constructor: Some : (a : Type) -> a -> Option(a)
Usage: #Some(I32(42))

Instantiation:
- Fresh var for 'a': α
- arg_ty becomes: α
- Check: I32(42) : α  ✓ (α = I32)
- ret_ty becomes: Option(α) = Option(I32)
```

---

## Alternatives Considered

### Alternative 1: Named Type Parameters

```gleam
CtrDef(
  params: [("a", Type), ("e", Type)],  // Named with kind
  arg_ty: ...,
  ret_ty: ...
)
```

**Rejected**: Adds complexity. De Bruijn indices are simpler.

### Alternative 2: Separate Type Constructor Registry

```gleam
type_constructors: [
  #("Option", TypeConstructor(["a"], ...)),
]
constructors: [
  #("Some", Constructor("Option", ...)),
]
```

**Rejected**: Over-engineered for current needs.

### Alternative 3: No Type Parameters (Current Simplified)

```gleam
#("Some", CtrDef([], Term(Typ(0), ...), Term(Typ(1), ...)))
```

**Status**: Current implementation. Works but loses type information.

---

## Open Questions

1. **Should we support full GADTs?** - Not for Phase 1. Simple polymorphism first.
2. **How to handle type inference?** - Use holes and unification (already in Core).
3. **What about kind checking?** - Defer to future work.

---

## Testing Strategy

### Unit Tests

```gleam
pub fn polymorphic_some_test() {
  // #Some(I32(42)) should have type Option(I32)
  let term = ctr("Some", i32(42, s0), s0)
  let #(_val, typ, _state) = infer(initial_state, term)
  // typ should be Option(I32)
}
```

### Integration Tests

```core
// examples/stdlib/option_example.core.tao
%let x = #Some(I32(42)) in
%let y = #None in
match(x, [
  (#Some(n), None, n),
  (#None, None, I32(0))
])
```

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Plan created |
| March 2026 | Implementation starting |
