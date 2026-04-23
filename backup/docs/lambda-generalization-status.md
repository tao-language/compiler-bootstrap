# Lambda Generalization Bug - Status Report

## Summary

The lambda generalization bug prevents Church numerals and higher-order functions from working correctly in the core language. This document describes the root cause, attempted fixes, and current workaround.

## Root Cause

When inferring types for nested lambdas like `k = x -> y -> x`, the HVar indices created during inner lambda generalization don't account for outer scope implicit parameters. This causes incorrect type inference:

**Expected type:** `∀a b. a → b → a` (Pi([], "x", Var(0), Pi([], "y", Var(1), Var(0))))
**Actual type:** `∀a b. a → b → b` (Pi([], "x", Var(0), Pi([], "y", Var(0), Var(0))))

### Technical Details

1. **Inner lambda generalization** (`y -> x`):
   - Creates hole h2 for y's type
   - Substitutes h2 → HVar(0)
   - x's type (h1) remains as HHole(h1) (not substituted, created by outer lambda)
   - Quotes to: `Pi([], "y", Var(0), Hole(h1))`

2. **Outer lambda generalization** (`x -> (y -> x)`):
   - Creates hole h1 for x's type
   - Substitutes h1 → HVar(0) in the inner VPi's codomain
   - Inner VPi becomes: `Pi([], "y", Var(0), HVar(0))`
   - Quotes to: `Pi([], "y", Var(0), Var(0))`
   - **Bug:** Var(0) in the inner domain references y, but Var(0) in the codomain should reference x (Var(1))

The core issue: HVar indices are relative to the current scope during generalization, but should be absolute positions in the full implicit parameter list.

## Attempted Fixes

### Option A: Offset-Aware Quoting (Partial Implementation)

Added `quote_domain_with_implicit_offset` function that converts HVar(i) to Var(i + offset), where offset is the number of outer implicit parameters.

**Status:** Implemented but not fully integrated. The offset calculation during generalization is complex because inner lambdas don't know about outer scope holes during their generalization.

### Option B: Shifted Substitution (Attempted)

Added `subst_value_with_hole_vars_shifted` function that shifts HVar indices when entering nested binders.

**Status:** Implemented but caused regressions. The shift was applied to ALL HVar indices, including newly substituted ones, causing incorrect types.

### Option C: Two-Phase Generalization (Not Implemented)

Defer inner lambda generalization until outer lambda has processed its holes. This would require significant refactoring of the type inference algorithm.

**Status:** Not implemented due to complexity.

## Current Workaround

Use explicit type annotations for nested polymorphic lambdas:

```typescript
// Instead of:
let k = x -> y -> x

// Use:
let k = (x: A) -> (y: B) -> x
```

This bypasses the hole generalization logic and produces correct types.

## Test Results

- **526 tests passing** (out of 533)
- **7 failures** related to Church numerals and higher-order functions:
  - `examples/core/programs/02_functions_and_currying.core.tao`
  - `examples/core/programs/13_vector_dependent.core.tao`
  - `examples/core/programs/17_type_annotation.core.tao`
  - `examples/core/programs/20_missing_match.core.tao`
  - `examples/core/programs/21_church_numerals.core.tao`
  - `examples/tao/programs/07_advanced/01_higher_order_functions.tao`
  - `examples/tao/programs/07_advanced/02_church_encoding.tao`

## Next Steps

1. **Deep dive into generalization algorithm**: Understand why the offset/shift approach isn't working correctly.

2. **Consider alternative representations**: Instead of HVar indices, use a representation that tracks absolute positions from the start.

3. **Implement two-phase generalization**: Collect all holes first, then substitute with absolute positions.

4. **Add more unit tests**: Create focused tests for the generalization logic to isolate the bug.

## References

- `docs/tao-lambda-generalization.md` - Detailed bug analysis
- `docs/plans/tao/lambda-generalization-fix.md` - Implementation plan
- `src/core/core.gleam` - Lines 2102-2155 (generalize_holes function)
