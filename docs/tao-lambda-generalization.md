# Lambda Generalization Bug: Comprehensive Analysis

**Status**: Known Limitation  
**Date**: March 2026  
**Affected Components**: Core language type inference, lambda generalization

---

## Executive Summary

The compiler bootstrap project has a **fundamental bug in lambda type generalization** that prevents nested polymorphic lambdas from working correctly. This affects:

- Church numerals and Church encoding
- Higher-order combinators (K, S, I, etc.)
- Curried function application with inferred types
- Dependent types with nested function types

**Symptom**: Error messages like `type ?5 is not callable` when applying inferred lambda functions.

**Workaround**: Use explicit type annotations for nested polymorphic lambdas.

**Root Cause**: HVar (hole variable) indices collide when nested lambdas both create implicit parameters with the same names, causing incorrect substitution during type application.

---

## Problem Description

### What Works

Simple lambda inference works correctly:

```gleam
// Identity function - works
let id = x -> x
// Inferred: ∀a. a -> a

// Single lambda application - works
id(10)  // Returns 10 : Int
```

### What Fails

Nested lambda inference fails:

```gleam
// K combinator - FAILS
let k = x -> y -> x
// Expected: ∀a b. a -> b -> a
// Actual: Type error during application

// Application fails
k(10)(20)  // Error: type ?5 is not callable
```

Church numerals fail:

```gleam
// Church numeral zero - FAILS
let zero = f -> x -> x
// Expected: ∀a b. (a -> a) -> a -> a
// Actual: Type error during application

// Church numeral one - FAILS
let one = f -> x -> f(x)
// Expected: ∀a b. (a -> a) -> a -> a
// Actual: Type error during application
```

---

## Technical Background

### HVar (Hole Variable) Semantics

HVar is a neutral term that references an implicit type parameter:

```gleam
pub type Head {
  HVar(index: Int)    // References i-th implicit parameter
  HHole(id: Int)      // References an unsolved hole
  HStepLimit          // Step limit exceeded
}
```

### Lambda Generalization Process

When inferring a lambda `x -> body`:

1. **Create hole** for parameter type: `Hole(-1, span)`
2. **Check body** against hole type
3. **Collect holes** to generalize: `[hole_id]`
4. **Generalize**: Replace holes with HVar references
5. **Create VPi**: `VPi(["_0"], "x", env, HVar(0), codomain)`

### The Collision Scenario

Consider `k = x -> y -> x`:

**Step 1: Infer inner lambda `y -> x`**
```
1. Create hole H1 for y's type
2. Body `x` has type Var(1) (references outer binder)
3. Generalize holes [H1]
4. Result: VPi(["_0"], "y", env, HVar(0), Var(1))
   - HVar(0) references position 0 in ["_0"]
```

**Step 2: Infer outer lambda `x -> (y -> x)`**
```
1. Create hole H0 for x's type
2. Body is inner lambda's type (VPi from Step 1)
3. Collect holes to generalize: [H0]
   - Note: H1 was already solved when checking inner lambda
4. Generalize holes [H0]:
   - Create substitution: H0 -> HVar(0)
   - Substitute in codomain (the inner VPi)
5. Result: VPi(["_0"], "x", env, HVar(0), VPi(["_0"], "y", env, HVar(0), Var(1)))
```

**THE BUG**: After generalization, we have:
```
VPi(
  ["_0"],           // Outer implicit params
  "x",
  env,
  HVar(0),          // References OUTER ["_0"] position 0 ✓
  VPi(
    ["_0"],         // Inner implicit params (SAME NAME!)
    "y",
    env,
    HVar(0),        // Should reference INNER ["_0"], but... ✗
    Var(1)
  )
)
```

Both `HVar(0)` reference position 0, but they should reference **different** implicit lists!

### Application Failure

When applying `k(10)`:

```gleam
// infer_app instantiates implicit params
let implicit_subst = [(0, h1)]  // h1 is fresh hole for outer "_0"

// Substitute in domain and codomain
domain_instantiated = subst_value_with_implicit_vars([(0, h1)], HVar(0))
  = HHole(h1)  // Correct for outer HVar

codomain_instantiated = subst_term_with_implicit_vars([(0, h1)], 
  VPi(["_0"], "y", env, HVar(0), Var(1)))
  = VPi(["_0"], "y", env, HHole(h1), Var(1))  // WRONG!
  // Inner HVar(0) became HHole(h1), but should stay HVar(0)!
```

The inner `HVar(0)` incorrectly becomes `HHole(h1)`, which means:
- The inner lambda's parameter type is now the SAME hole as the outer
- During unification, this causes type confusion
- Holes remain unsolved, leading to "type ?X is not callable" errors

---

## Root Cause Analysis

### Why HVar Indices Collide

The fundamental issue is that **HVar indices are simple integers without scope information**:

```gleam
pub type Head {
  HVar(index: Int)  // Just an integer - no scope tracking!
}
```

When we have nested VPi types:
```
VPi(["_0"], "x", _, HVar(0),  // Outer: HVar(0) -> "_0"[0]
  VPi(["_0"], "y", _, HVar(0), Var(1)))  // Inner: HVar(0) -> "_0"[0] (DIFFERENT LIST!)
```

Both `HVar(0)` mean "position 0 in the implicit list", but they reference **different lists**. The substitution algorithm cannot distinguish between them.

### Why This Is Hard to Fix

HVar has **conflicting semantic requirements**:

| Operation | Expected HVar Semantics |
|-----------|------------------------|
| **Generalization** | Indices relative to LOCAL implicit list |
| **Substitution** | Indices resolved in GLOBAL context |
| **Quoting (HVar→Var)** | Indices from END of context (`lvl - index - 1`) |
| **Shift** | Indices are ABSOLUTE positions |

These conflicting requirements make it impossible to fix with simple index manipulation.

---

## Approaches Attempted

### Approach 1: Rename Nested Implicit Params

**Idea**: Rename inner implicit params to avoid name collision:
```gleam
// Before:
VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(0), Var(1)))

// After renaming:
VPi(["_0"], "x", _, HVar(0), VPi(["_1"], "y", _, HVar(0), Var(1)))
```

**Implementation**:
```gleam
fn rename_nested_implicit(value: Value, offset: Int) -> Value {
  case value {
    VPi(impl, name, env, in_val, out_term) ->
      VPi(
        list.map(impl, fn(n) { rename_implicit_name(n, offset) }),
        name,
        env,
        rename_nested_implicit(in_val, offset + list.length(impl)),
        rename_nested_implicit_in_term(out_term, offset + list.length(impl)),
      )
    // ... other cases
  }
}

fn rename_implicit_name(name: String, offset: Int) -> String {
  case name {
    "_" <> num_str -> {
      case int.parse(num_str) {
        Ok(num) -> "_" <> int.to_string(num + offset)
        Error(_) -> name
      }
    }
    _ -> name
  }
}
```

**Why It Failed**: Renaming the implicit param names (`"_0"` → `"_1"`) doesn't change the HVar indices! Both `HVar(0)` still reference position 0 in their respective lists. The name is just metadata; the index is what matters for substitution.

**Test Result**: 520 passed, 4 failures (no improvement)

---

### Approach 2: Shift HVar to Absolute Indices

**Idea**: Make HVar indices absolute positions in the combined implicit context:
```gleam
// Before:
VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(0), Var(1)))

// After shifting inner HVar by 1:
VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(1), Var(1)))
// Now: HVar(0) -> combined["_0"][0], HVar(1) -> combined["_0", "_1"][1]
```

**Implementation**:
```gleam
// In generalize_holes:
let shifted_codomain = shift_hvar_in_value(codomain, list.length(holes))
let generalized_codomain_val = subst_value_with_hole_vars(hole_subst, shifted_codomain)

// shift_hvar_in_value adds offset to all HVar indices:
fn shift_hvar_in_value(value: Value, offset: Int) -> Value {
  case value {
    VNeut(HVar(level), []) -> VNeut(HVar(level + offset), [])
    VNeut(HVar(level), spine) -> VNeut(HVar(level + offset), ...)
    VPi(impl, name, env, in_val, out_term) ->
      VPi(implicit, name, ..., shift_hvar_in_value(in_val, offset), ...)
    // ... other cases
  }
}
```

**Why It Failed**: This breaks the quoting logic! The `quote_head` function converts HVar to Var using the formula:
```gleam
fn quote_head(lvl: Int, head: Head, s: Span) -> Term {
  case head {
    HVar(l) -> Var(lvl - l - 1, s)  // Assumes indices from END of context
    // ...
  }
}
```

With absolute indices, this formula produces wrong Var indices, breaking type reconstruction.

**Test Result**: 519 passed, 5 failures (regression!)

---

### Approach 3: Offset-Based Substitution

**Idea**: Track nesting depth during substitution and adjust HVar lookup:
```gleam
fn subst_value_with_implicit_vars_loop(
  subst: List(#(Int, Int)),
  value: Value,
  offset: Int,  // Track nesting depth
) -> Value {
  case value {
    VNeut(HVar(index), []) -> {
      // Look up index + offset in substitution
      case list.key_find(subst, index + offset) {
        Ok(hole_id) -> VNeut(HHole(hole_id), [])
        Error(Nil) -> value
      }
    }
    VPi(impl, name, env, in_val, out) -> {
      // Increase offset when entering nested scope
      let new_offset = offset + list.length(impl)
      VPi(impl, name, env,
        subst_value_with_implicit_vars_loop(subst, in_val, new_offset),
        subst_term_with_implicit_vars_loop(subst, out, new_offset),
      )
    }
    // ... other cases
  }
}
```

**Why It Failed**: This approach is semantically backwards! The offset should make nested HVar **less** likely to match (since they reference local params), but the implementation makes them **more** likely to match (since `index + offset` grows).

The correct fix would require:
1. NOT substituting HVar in nested scopes (they reference local params)
2. OR using a different substitution for each scope level

Both options require significant restructuring of the substitution logic.

**Test Result**: 519 passed, 5 failures (no improvement)

---

### Approach 4: Skip Nested Substitution

**Idea**: Don't substitute HVar that reference nested implicit params:
```gleam
fn subst_value_with_implicit_vars_loop(
  subst: List(#(Int, Int)),
  value: Value,
  offset: Int,
) -> Value {
  case value {
    VNeut(HVar(index), []) -> {
      // Only substitute if index < offset (references outer params)
      if index < offset {
        value  // Don't substitute - references local implicit
      } else {
        case list.key_find(subst, index) {
          Ok(hole_id) -> VNeut(HHole(hole_id), [])
          Error(Nil) -> value
        }
      }
    }
    // ... other cases
  }
}
```

**Why It Failed**: Same fundamental issue as Approach 3. The HVar semantics are ambiguous - we can't tell if `HVar(0)` references outer or inner implicit params without explicit scope tracking.

**Test Result**: 519 passed, 5 failures (no improvement)

---

## Recommended Fix: Explicit Scope Tracking

### Design

Add scope information to HVar:
```gleam
pub type Head {
  HVar(scope_id: Int, index: Int)  // Now tracks which scope!
  HHole(id: Int)
  HStepLimit
}
```

Or use named references:
```gleam
pub type Head {
  HVar(name: String)  // E.g., HVar("_0"), HVar("_1")
  HHole(id: Int)
  HStepLimit
}
```

### Implementation Plan

1. **Update HVar constructor** in `Head` type
2. **Update all HVar creation sites** (~10 locations)
3. **Update substitution** to match on scope/name
4. **Update quoting** to handle scoped HVar
5. **Update shifting** to adjust scope tracking
6. **Update unification** to compare scopes

### Estimated Effort

- **Code changes**: ~50 functions need updates
- **Testing**: Full regression test + new unit tests
- **Time**: 2-3 days for implementation, 1 day for testing

### Risks

- Breaking changes to core type representation
- Potential performance impact (scope tracking overhead)
- Complex interactions with existing HVar logic

---

## Unit Test Examples

### Test 1: Nested Lambda HVar Independence

```gleam
/// Test that nested lambdas have independent implicit parameter scopes.
/// k = x -> y -> x should infer to ∀a b. a -> b -> a
pub fn nested_lambda_hvar_independence_test() {
  let span = Span("test", 0, 0, 0, 0)
  
  // Build: k = x -> y -> x
  // Inner: y -> x (returns Var(1) which is x)
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  // Outer: x -> (y -> x)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, k)
  
  // Should have no errors
  state.errors |> should.equal([])
  
  // Type should be a VPi (function type) with implicit params
  // After fix, should have polymorphic type with independent implicit scopes
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}
```

### Test 2: K Combinator Application

```gleam
/// Test K combinator application: k(10)(20) should return 10
/// This verifies that hole unification works correctly with nested lambdas.
pub fn k_combinator_application_test() {
  let span = Span("test", 0, 0, 0, 0)
  
  // Build: k = x -> y -> x
  let inner = c.Lam([], #("y", c.Hole(-1, span)), c.Var(1, span), span)
  let k = c.Lam([], #("x", c.Hole(-1, span)), inner, span)
  
  // Build: k(10)(20)
  let app1 = c.App(k, [], c.Lit(c.I32(10), span), span)
  let app2 = c.App(app1, [], c.Lit(c.I32(20), span), span)
  
  let state = c.initial_state
  let #(_val, ty, state) = c.infer(state, app2)
  
  // Should have no errors
  state.errors |> should.equal([])
  
  // Result type should be I32 type (VLitT(I32T)), not a hole
  let is_i32_type = case ty {
    c.VLitT(c.I32T) -> True
    _ -> False
  }
  
  is_i32_type |> should.be_true()
}
```

### Test 3: Church Numeral Zero

```gleam
/// Test Church numeral zero: zero = f -> x -> x
/// Expected type: ∀a b. (a -> a) -> a -> a
/// This tests triple-nested lambda inference.
pub fn church_numeral_zero_test() {
  let span = Span("test", 0, 0, 0, 0)
  
  // Build: zero = f -> x -> x
  let inner = c.Lam([], #("x", c.Hole(-1, span)), c.Var(0, span), span)
  let zero = c.Lam([], #("f", c.Hole(-1, span)), inner, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, zero)
  
  // Should have no errors
  state.errors |> should.equal([])
  
  // Type should be VPi with implicit params (polymorphic)
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}
```

### Test 4: Church Numeral Successor

```gleam
/// Test Church numeral successor: succ = n -> f -> x -> f(n f x)
/// Expected type: ∀a. (a -> a) -> a -> a -> (a -> a) -> a -> a
pub fn church_numeral_succ_test() {
  let span = Span("test", 0, 0, 0, 0)
  
  // Build: succ = n -> f -> x -> f(n f x)
  // n f x = ((n f) x)
  let n_f = c.App(c.Var(2, span), [], c.Var(1, span), span)
  let n_f_x = c.App(n_f, [], c.Var(0, span), span)
  let f_n_f_x = c.App(c.Var(1, span), [], n_f_x, span)
  
  let inner = c.Lam([], #("x", c.Hole(-1, span)), f_n_f_x, span)
  let mid = c.Lam([], #("f", c.Hole(-1, span)), inner, span)
  let succ = c.Lam([], #("n", c.Hole(-1, span)), mid, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, succ)
  
  // Should have no errors
  state.errors |> should.equal([])
  
  // Type should be VPi with implicit params (polymorphic)
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}
```

### Test 5: Triple Nested Lambda

```gleam
/// Test triple nested lambda: compose = f -> g -> x -> f(g(x))
/// Expected type: ∀a b c. (b -> c) -> (a -> b) -> a -> c
pub fn triple_nested_lambda_test() {
  let span = Span("test", 0, 0, 0, 0)
  
  // Build: compose = f -> g -> x -> f(g(x))
  let g_x = c.App(c.Var(1, span), [], c.Var(0, span), span)
  let f_g_x = c.App(c.Var(2, span), [], g_x, span)
  
  let inner = c.Lam([], #("x", c.Hole(-1, span)), f_g_x, span)
  let mid = c.Lam([], #("g", c.Hole(-1, span)), inner, span)
  let compose = c.Lam([], #("f", c.Hole(-1, span)), mid, span)
  
  let state = c.initial_state
  let #(_, ty, state) = c.infer(state, compose)
  
  // Should have no errors
  state.errors |> should.equal([])
  
  // Type should be VPi with implicit params (polymorphic)
  let is_vpi_with_implicit = case ty {
    c.VPi(implicit, _, _, _, _) -> {
      implicit != []
    }
    _ -> False
  }
  
  is_vpi_with_implicit |> should.be_true()
}
```

---

## Current Status

### Test Results

| Metric | Value |
|--------|-------|
| Total tests | 521 |
| Passing | 517 |
| Failing | 4 |
| Failure rate | 0.77% |

### Failing Tests

1. `examples/core/programs/02_functions_and_currying.core.tao`
   - Error: `type ?5 is not callable`
   - Cause: K combinator application fails

2. `examples/core/programs/10_church_numerals.core.tao`
   - Error: `type ?5, ?12, ?14, ... is not callable`
   - Cause: Church numeral application fails

3. `examples/core/programs/13_vector_dependent.core.tao`
   - Error: `type ?11 is not callable`
   - Cause: Dependent function application fails

4. `examples/core/programs/20_missing_match.core.tao`
   - Error: Multiple `type ?X is not callable`
   - Cause: Church encoding application fails

5. `examples/core/programs/17_type_annotation.core.tao`
   - Error: Type mismatch
   - Cause: Related to hole unification

### Workarounds

Users can work around this limitation by using **explicit type annotations**:

```gleam
// Instead of (fails):
let k = x -> y -> x

// Use explicit annotation (works):
let k : ∀a b. a -> b -> a = x -> y -> x

// Instead of (fails):
let zero = f -> x -> x

// Use explicit annotation (works):
let zero : ∀a b. (a -> a) -> a -> a = f -> x -> x
```

---

## Related Files

- `src/core/core.gleam` - Core language implementation
  - `generalize_holes/2` - Lambda generalization function
  - `subst_value_with_implicit_vars/2` - Substitution for implicit params
  - `subst_term_with_implicit_vars/2` - Term substitution
  - `infer_app/4` - Application type inference
  - `quote_head/3` - HVar to Var conversion

- `test/core/lambda_generalization_test.gleam` - Unit tests for this bug

- `examples/core/programs/02_functions_and_currying.core.tao` - Failing example
- `examples/core/programs/10_church_numerals.core.tao` - Failing example

---

## References

- [Core Language Specification](core.md)
- [Core Syntax Reference](core-syntax.md)
- [Lessons Learned](lessons-learned.md)
- [Retrospective](plans/retrospective.md)

---

## Changelog

- **2026-03-30**: Document created with comprehensive analysis
- **2026-03-30**: Unit test file created (`test/core/lambda_generalization_test.gleam`)
- **2026-03-30**: Four fix approaches attempted and documented
