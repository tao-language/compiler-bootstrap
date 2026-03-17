# Core Language Type Inference Failures Analysis

**Date**: 2026-03-16  
**Status**: 14 failing tests (out of 516 total)  
**Test Results**: 502 passed, 14 failures

## Overview

The remaining test failures fall into three categories related to the core language's type inference system:

1. **Lambda Type Inference** (2 failures) - Holes not properly generalized to implicit type variables
2. **Match Expression Inference** (6 failures) - Dependent pattern matching with holes
3. **Type Unification** (2 failures) - Pi types with holes not unifying correctly
4. **Pattern Match Dependent Motives** (4 failures) - Dependent type inference in patterns

---

## Category 1: Lambda Type Inference

### Test: `lam_infer_known_test`

**Location**: `test/core/core_test.gleam:1005`

#### Expected Behavior
```gleam
#(
  VLam([], "x", [], i32(1, s1)),
  VPi([], "x", [], vhole(0), i32t(s1)),  // Empty implicit params list
  State(..s, hole: 1, var: 1, ctx: [#("x", #(vvar(0), vhole(0)))])
)
```

#### Actual Behavior
```gleam
#(
  VLam([], "x", [], i32(1, s1)),
  VPi(["_0"], "x", [], VNeut(HVar(0), []), i32t(s1)),  // Has ["_0"] implicit param
  State(..s, hole: 1, var: 1, ctx: [#("x", #(VNeut(HVar(0), []), vhole(0)))])
)
```

#### Root Cause
When inferring the type of a lambda with a known body type (like `I32`), the current implementation:
1. Creates a hole for the parameter type
2. Generalizes the hole to an implicit type variable (`HVar(0)` named `"_0"`)
3. Adds this implicit parameter to the `VPi` type

However, when the body type is concrete (not dependent on the parameter), the implicit parameter should **not** be added to the `VPi`. The hole should remain as `HHole(0)` without creating an implicit parameter.

#### Why This Happens
The lambda generalization in `infer()` currently:
1. Collects all free holes in the body type
2. Converts them to implicit type variables unconditionally
3. Wraps the result type in a `VPi` with these implicit parameters

This is correct for dependent types but incorrect when the body doesn't depend on the parameter.

#### How to Fix
**Option A: Dependency Analysis** (Recommended)
- Before generalizing, check if the body type actually contains the hole
- Only add implicit parameters for holes that appear free in the body
- Use `free_holes_term()` or similar to detect actual dependencies

**Option B: Post-processing** (Simpler)
- After generalization, check if implicit parameters are used in the body
- Remove unused implicit parameters from the `VPi`

**Implementation Steps**:
1. Add a function `holes_in_term(holes: List(Int), term: Term) -> Bool` to check if specific holes appear in a term
2. Modify `infer()` lambda case to filter implicit parameters based on actual usage
3. Update `VPi` construction to only include used implicit parameters

---

### Test: `lam_infer_unknown_test`

**Location**: `test/core/core_test.gleam:1016`

#### Expected Behavior
Lambda with unknown body type (`var(0, s1)` referring to parameter) should:
- Return `VLam` with body containing `Var(-1)` (De Bruijn index 0, shifted to -1)
- Type should be `VPi` with `HHole(0)` as domain (not `HVar`)
- Pattern match should succeed

#### Actual Behavior
- Returns `False` from pattern match
- Likely has `HVar` instead of `HHole` in the type

#### Root Cause
Same as `lam_infer_known_test` - holes are being generalized to implicit type variables even when they shouldn't be.

#### How to Fix
Same fix as `lam_infer_known_test` - only generalize holes that create actual dependencies.

---

## Category 2: Match Expression Inference

### Tests: `infer_match_empty_test`, `infer_match_unbound_test`, `infer_match_bound_test`

**Location**: `test/core/core_test.gleam:1520-1580`

#### Expected Behavior
- `infer_match_empty_test`: Matching with empty cases should fail with error
- `infer_match_unbound_test`: Matching with unbound variable should fail
- `infer_match_bound_test`: Matching with bound variable should succeed

All tests expect `True` but get `False`.

#### Actual Behavior
All return `False` from their pattern matches, indicating the inference result doesn't match expected structure.

#### Root Cause
The `infer()` function for `Match` expressions likely:
1. Doesn't properly handle the motive type
2. Doesn't correctly instantiate implicit parameters when checking cases
3. May not be accumulating errors correctly

#### How to Fix
1. Review `infer()` Match case in `src/core/core.gleam`
2. Ensure motive is checked/inferred before cases
3. Verify implicit parameter instantiation for each case body
4. Check that errors are accumulated in state, not causing early return

**Implementation Steps**:
1. Add debug output to understand current Match inference behavior
2. Compare with `check()` Match case (which works for exhaustiveness)
3. Ensure `infer_match` properly handles dependent motives
4. Add proper error accumulation

---

### Tests: `match_check_mismatch_test`, `check_lam_mismatch_test`

**Location**: `test/core/core_test.gleam:1560, 1100`

#### Expected Behavior
- Type mismatch errors should be recorded in state
- Return value should be `VErr`

#### Actual Behavior
The error is recorded but the state structure differs:
- Expected: `VPi([], "x", [], VNeut(HHole(0), []), Hole(0, ...))`
- Actual: `VPi(["_0"], "x", [], VNeut(HVar(0), []), Var(0, ...))`

#### Root Cause
Same root cause as lambda tests - holes are being generalized to implicit type variables (`HVar`) when they should remain as holes (`HHole`).

#### How to Fix
Same fix as lambda tests - proper dependency analysis before generalization.

---

## Category 3: Type Unification

### Test: `unify_pi_with_holes_test`

**Location**: `test/core/core_test.gleam:1750`

#### Expected Behavior
```gleam
Ok(VLitT(I32T))
```

Unifying a Pi type with holes should succeed and return the concrete type.

#### Actual Behavior
```gleam
Error(Nil)
```

Unification fails.

#### Root Cause
The `unify()` function likely doesn't handle `VPi` types with holes correctly:
1. May not be instantiating implicit parameters before unification
2. May not be handling `HVar` (implicit type variables) vs `HHole` (holes) correctly
3. May be failing when trying to unify a Pi type with a literal type

#### How to Fix
1. Review `unify()` function for `VPi` case
2. Ensure implicit parameters are instantiated with fresh holes before unification
3. Handle the case where a Pi type with holes should unify with a concrete type
4. Add proper error messages for unification failures

**Implementation Steps**:
1. Add `instantiate_implicit(subst: Subst, typ: Value) -> Value` function
2. Modify `unify()` to instantiate implicit parameters before comparing
3. Add special case for unifying `VPi` with holes against concrete types
4. Ensure proper error reporting

---

## Category 4: Pattern Match Dependent Motives

### Tests: `match_dependent_motive_with_var_test`, `match_hole_motive_infer_int_test`, `match_hole_motive_infer_string_test`, `match_dependent_motive_explicit_test`

**Location**: `test/core/pattern_match_test.gleam:250-350`

#### Expected Behavior
- Pattern matching with dependent motives should infer correct types
- Hole motives should be inferred from the scrutinee type
- Both explicit and implicit dependent motives should work

#### Actual Behavior
All tests return `False`, indicating the check/infer result doesn't match expected structure.

#### Root Cause
The `check()` function for `Match` expressions with dependent motives:
1. Doesn't properly instantiate the motive type for each case
2. Doesn't correctly handle hole motives (should infer from scrutinee)
3. May not be properly binding the motive variable in each case context

#### How to Fix
1. Review `check()` Match case in `src/core/core.gleam`
2. Ensure motive is instantiated with scrutinee value before checking cases
3. For hole motives, infer the motive type from scrutinee type
4. Properly bind motive variable in case context

**Implementation Steps**:
1. Add `instantiate_motive(motive: Value, scrutinee: Value) -> Value` function
2. Modify `check()` Match case to instantiate motive before checking cases
3. Add hole motive inference from scrutinee type
4. Ensure proper variable binding in case bodies

---

## Implementation Priority

### Phase 1: Fix Lambda Generalization (Highest Priority)
**Estimated Impact**: Fixes 4 tests (lam_infer_*, check_*_mismatch)

1. Add `holes_in_term()` helper function
2. Modify lambda `infer()` to only generalize used holes
3. Update tests to verify correct behavior

### Phase 2: Fix Match Expression Inference
**Estimated Impact**: Fixes 6 tests (infer_match_*, match_check_*)

1. Review and fix `infer()` Match case
2. Ensure proper motive handling
3. Add error accumulation

### Phase 3: Fix Type Unification
**Estimated Impact**: Fixes 1 test (unify_pi_with_holes)

1. Add implicit parameter instantiation
2. Fix `unify()` for VPi types
3. Handle hole unification

### Phase 4: Fix Dependent Pattern Matching
**Estimated Impact**: Fixes 4 tests (match_dependent_*, match_hole_*)

1. Add motive instantiation
2. Fix hole motive inference
3. Ensure proper variable binding

---

## Key Concepts

### Holes vs Implicit Type Variables

| Concept | Syntax | Semantics | When Used |
|---------|--------|-----------|-----------|
| **Hole** | `HHole(id)` | Unknown type to be solved | During type checking, before generalization |
| **Implicit Type Variable** | `HVar(id)` or `VNeut(HHole(id), [])` | Generalized hole, becomes implicit parameter | After lambda generalization, for dependent types |
| **Implicit Parameter** | `VPi(["_0"], ...)` | Lambda parameter that's inferred | When body depends on parameter type |

### Generalization Rule

**Correct**: Only generalize holes that appear free in the body type.

```gleam
// x: _ -> 42
// Body is I32, doesn't contain hole
// Should NOT generalize - keep as HHole
infer(λx. 42) = (VLam(x, 42), VPi([], x, [], HHole(0), I32T))

// x: _ -> x
// Body contains hole (depends on x)
// SHOULD generalize - create implicit param
infer(λx. x) = (VLam(x, x), VPi(["_0"], x, [], HVar(0), HVar(0)))
```

### De Bruijn Indices

- **Syntax (Term)**: Variables use non-negative indices (0, 1, 2, ...)
- **Semantics (Value)**: Variables use negative indices (-1, -2, ...) for bound variables
- **Implicit type parameters**: Separate namespace, don't affect value variable indices

---

## Test Commands

```bash
# Run specific failing tests
gleam test --filter lam_infer_known
gleam test --filter unify_pi_with_holes
gleam test --filter match_dependent_motive

# Run all core tests
gleam test --filter core@

# Continuous testing
fswatch -or src/core test/core | xargs -n1 -I{} gleam test
```

---

## References

- [Core Language Specification](../../docs/core.md)
- [Normalization by Evaluation](../../docs/core.md#normalization-by-evaluation)
- [Bidirectional Type Checking](../../docs/core.md#bidirectional-type-checking)
- [Lessons Learned](../../docs/lessons-learned.md) - Important warnings about previous fixes
