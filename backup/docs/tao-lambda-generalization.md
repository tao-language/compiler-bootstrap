# Lambda Generalization Bug: Comprehensive Analysis

**Status**: Root Cause Identified - Fix Planned (Option A)  
**Date**: March 2026  
**Affected Components**: Core language type inference, lambda generalization, quoting

---

## Executive Summary

The compiler bootstrap project has a **fundamental bug in lambda type generalization** that prevents nested polymorphic lambdas from working correctly. This affects:

- Church numerals and Church encoding
- Higher-order combinators (K, S, I, etc.)
- Curried function application with inferred types
- Dependent types with nested function types

**Symptom**: Error messages like `type ?5 is not callable` when applying inferred lambda functions.

**Workaround**: Use explicit type annotations for nested polymorphic lambdas.

**Root Cause**: HVar (hole variable) indices are created as **relative positions** within their scope during quoting, but during substitution in `infer_app`, only outer implicit params are instantiated, causing inner HVar indices to incorrectly match the outer substitution.

**Fix**: Modify `quote_domain_with_implicit` to create **absolute HVar indices** that track the total number of implicit parameters from all outer scopes. See [docs/plans/tao/lambda-generalization-fix.md](docs/plans/tao/lambda-generalization-fix.md) for detailed implementation plan.

---

## Investigation Status (March 31, 2026)

### Attempted Fixes

| Approach | Result | Issue |
|----------|--------|-------|
| Shift-only substitution | 523 passed, 10 failures | Inner implicit params never instantiated |
| Shift + recursive instantiation | 523 passed, 10 failures | Complex state threading, type mismatches |
| Absolute HVar indices | Planned | Requires quoting logic changes |

### Current State

- **526 tests passing, 7 failures** (98.7% pass rate)
- **Root cause identified**: Relative HVar indices collide during substitution
- **Fix planned**: Option A - absolute HVar indices in quoting

---

## Root Cause Analysis

### HVar Semantics

**HVar(i)** is a De Bruijn-like index for implicit parameters:
- References the i-th implicit parameter from the current scope
- Like `Var(i)` for explicit binders, but for implicit type parameters

### The Bug

**Example**: `k = x -> y -> x`

1. **During generalization** (`generalize_holes`):
   ```
   holes = [h1, h2]
   hole_subst = [(h1, 0), (h2, 1)]
   
   // After subst_value_with_hole_vars (NO SHIFT):
   VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(0), Var(1)))
   //                                    ^^^^ Should be HVar(1) after shift!
   ```

2. **During application** (`infer_app`):
   ```
   implicit_subst = [(0, h1)]  // Only outer implicit instantiated
   
   // Both HVar(0) match (0, h1):
   VPi(["_0"], "x", _, HHole(h1), VPi(["_0"], "y", _, HHole(h1), Var(1)))
   // Inner implicit never gets its own hole!
   ```

3. **Result**: Type error "type ?X is not callable" because both implicit params share the same hole.

### Why Simple Fixes Fail

**Shift-only approach**: Adding shift to lookup (`index + shift`) prevents inner HVar from matching outer substitution, BUT inner implicit params are never instantiated, leaving holes unsolved.

**Recursive instantiation**: Creating holes for nested implicit params requires threading State through substitution, which is complex and error-prone.

---

## Planned Fix: Option A (Absolute HVar Indices)

### Core Idea

Modify `quote_domain_with_implicit` to track an **offset** representing the total number of implicit parameters from outer scopes. HVar indices become **absolute positions** in the combined context.

### Key Changes

1. **Add offset parameter** to `quote_domain_with_implicit`
2. **Add shifted hole substitution** functions
3. **Update `generalize_holes`** to use shifted substitution
4. **Update `infer_app`** to use shifted implicit substitution

### Expected Results

- **Before**: 526 passed, 7 failures
- **After**: 533+ passed, 0 failures

See [docs/plans/tao/lambda-generalization-fix.md](docs/plans/tao/lambda-generalization-fix.md) for detailed implementation plan.

---

## Problem Description

### Affected Programs

1. **Church Numerals** (`examples/tao/programs/10_church_numerals.core.tao`)
   - `zero = f -> x -> x`
   - `succ = n -> f -> x -> f(n f x)`
   - Fails with "type ?X is not callable"

2. **K Combinator** (`examples/tao/programs/02_functions_and_currying.core.tao`)
   - `k = x -> y -> x`
   - `k(10)(20)` should return `10`
   - Fails with "type ?X is not callable"

3. **Dependent Types** (`examples/tao/programs/13_vector_dependent.core.tao`)
   - Nested polymorphic functions with dependent types
   - Fails with type errors

### Error Messages

```
error[E0103]: Cannot call non-function value
  = note: This value has type ?164, which is not callable
  = note: Only function values (created with ->) can be called with parentheses
```

```
error[E0107]: Infinite type
  = note: Hole #160 would create an infinite type
  = note: This happens when a type refers to itself
```

---

## Technical Details

### Type Inference Flow

1. **Lambda inference** (`infer`):
   - Create hole for domain type
   - Infer codomain type
   - Call `generalize_holes` to abstract over holes

2. **Generalization** (`generalize_holes`):
   - Create substitution: `hole_id → HVar(index)`
   - Apply substitution to domain and codomain
   - Quote codomain to syntax

3. **Application** (`infer_app`):
   - Instantiate implicit params with fresh holes
   - Apply substitution to domain and codomain
   - Check argument against domain
   - Evaluate codomain with argument

### Where the Bug Occurs

The bug occurs in **step 2** (generalization) when quoting the codomain:

```gleam
// In quote_domain_with_implicit:
VPi(impl, name, in_val, out) -> {
  // HVar indices in in_val are relative to OUTER scope
  // HVar indices in out are relative to INNER scope (after impl binders)
  // BUT: No offset is tracked, so both use the same indices!
}
```

### Correct Behavior

With absolute HVar indices:

```
// k = x -> y -> x
// After generalization (CORRECT):
VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(1), Var(1)))
// HVar(0) references outer _0 (absolute position 0)
// HVar(1) references inner _0 (absolute position 1)

// During k(10) application:
// implicit_subst = [(0, h1)]  // Instantiate outer _0
// HVar(0) → HHole(h1) ✓
// HVar(1) → no match, preserved ✓
// Inner implicit gets its own hole h2
```

---

## Test Coverage

### Existing Tests

- **526 tests passing** (98.7%)
- Tests cover basic type inference, pattern matching, exhaustiveness

### Missing Tests (Added as Regression Tests)

- `test/core/hvar_fix_test.gleam`:
  - `k_combinator_type_structure_test`
  - `k_combinator_application_test`
  - `church_numeral_zero_test`
  - `compose_combinator_test`
  - `church_numeral_succ_application_test`

---

## Related Documentation

- [Core Language Specification](docs/core.md) - Core language semantics
- [Tao Syntax Specification](docs/tao-syntax.md) - Tao language syntax
- [Lambda Generalization Fix Plan](docs/plans/tao/lambda-generalization-fix.md) - Detailed fix plan

---

## History

- **March 2026**: Bug identified during Church numeral implementation
- **March 30, 2026**: Initial investigation, shift-only fix attempted (failed)
- **March 31, 2026**: Root cause identified, Option A planned
