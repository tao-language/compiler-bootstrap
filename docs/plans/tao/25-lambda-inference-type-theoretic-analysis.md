# Lambda Inference: Type-Theoretic Analysis

> **Date**: March 2026
> **Status**: 📋 Deep Analysis Complete

---

## Type-Theoretic Foundation

### The Problem in Type Theory

In dependently typed lambda calculus, a lambda abstraction has the form:

```
λx:A. b : Πx:A. B
```

Where:
- `A` is the domain type (parameter type)
- `B` is the codomain type (body type, possibly depending on `x`)
- `Πx:A. B` is the dependent function type

**Key Insight**: The domain `A` must be known BEFORE we can type the lambda. We cannot infer `A` from the body alone because:
1. The body might not use `x` (constant function)
2. The body might use `x` in a way that's consistent with multiple types
3. In dependent type theory, `A` can be any type, not just simple types

### Current Approach: Hole-Based Inference

Our current approach:
1. Create a hole for `A`: `A = ?0`
2. Type the body in context `x : ?0`
3. Get body type `B`
4. Generalize holes in `?0` and `B` to implicit parameters

**Problem**: This approach assumes holes can be "solved" by generalization, but generalization doesn't solve holes—it replaces them with implicit parameters. The hole `?0` becomes `α_0` (an implicit type variable), but this is only correct if `?0` was meant to be polymorphic.

### Why This Fails for Nested Lambdas

For nested lambdas `λx:A. λy:B. body`:

1. Outer lambda creates hole `?0` for `A`
2. Inner lambda creates hole `?1` for `B`
3. Inner lambda generalizes: `?1 → α_0` (first implicit)
4. Inner lambda returns type: `Πy:α_0. Bool`
5. Outer lambda receives body type: `Πy:α_0. Bool`
6. Outer lambda tries to generalize `?0` and holes in `Πy:α_0. Bool`

**Critical Issue**: The inner lambda's `α_0` is already bound to the inner lambda's first implicit parameter. When the outer lambda generalizes, it creates NEW implicit parameters `β_0, β_1, ...`. The substitution should map:
- `?0 → β_0` (outer's first implicit)
- `?1 → β_1` (outer's second implicit)

But `?1` was already replaced with `α_0` in the inner lambda's type! So the outer lambda's substitution doesn't affect the inner lambda's type.

### The Correct Approach: Context-Aware Generalization

In proper type theory, when we have nested binders, we need to:

1. **Track the context depth**: Each lambda adds a new binder to the context
2. **Adjust implicit indices**: Inner lambda's implicits are relative to its context, not the outer context
3. **Lift inner types**: When returning from inner lambda, lift its type to the outer context

This is exactly what De Bruijn index shifting does, but we need to apply it to IMPLICIT PARAMETERS, not just term variables.

## Options for Correctness

### Option 1: Require Explicit Type Annotations (Most Sound)

**Approach**: Don't infer lambda parameter types. Require:
```tao
fn not(b: Bool) -> Bool { ... }
```

**Pros**:
- Sound and complete
- No ambiguity
- Matches how dependently typed languages work (Agda, Idris, Coq)

**Cons**:
- Less convenient for users
- Breaks existing code

**Verdict**: **RECOMMENDED for correctness**. This is how proper dependently typed languages work.

### Option 2: Two-Phase Inference with Constraints

**Approach**:
1. First pass: Collect constraints (e.g., "`?0` must unify with `Bool`")
2. Second pass: Solve all constraints simultaneously

**Pros**:
- Can handle mutual dependencies
- More complete inference

**Cons**:
- Complex implementation
- Still can't infer all types (undecidable in general)

**Verdict**: Good middle ground, but complex.

### Option 3: Fix Current Approach with Proper Lifting

**Approach**: Fix the hole generalization to properly lift inner lambda types.

**Implementation**:
```gleam
// After inferring inner lambda
let #(body_val, body_ty, s) = infer(s, body)

// Lift body_ty to outer context by shifting implicit indices
let num_outer_implicits = list.length(holes_to_generalize)
let body_ty_lifted = shift_implicit_indices(body_ty, num_outer_implicits)

// Now generalize with lifted type
```

**Pros**:
- Maintains current inference behavior
- Less disruptive

**Cons**:
- Still incomplete (can't infer all types)
- Complex to get right

**Verdict**: **RECOMMENDED for practical fix**. Fixes the immediate bug while maintaining usability.

### Option 4: Bidirectional Type Checking

**Approach**: Use bidirectional typing with synthesis and checking modes:
- **Synthesize**: Infer type from term
- **Check**: Verify term has expected type

For lambdas:
- If expected type is `Πx:A. B`, check lambda against it (use `A` from expected type)
- If no expected type, fail (require annotation)

**Pros**:
- Clear semantics
- Good error messages
- Standard approach in modern type checkers

**Cons**:
- Significant refactoring
- Still requires annotations for some lambdas

**Verdict**: **RECOMMENDED for long-term architecture**.

## Root Cause Analysis

### The Specific Bug

Looking at the error:
```
InfiniteType(4, VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
  VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
    VNeut(HHole(4), []), Hole(5, ...)), Hole(3, ...)))
```

The inner VPi has `in_val = VNeut(HHole(4), [])`. This means:
1. Hole 4 was created for outer lambda's parameter
2. Hole 4 appears in inner lambda's type (somehow)
3. Hole 4 was NOT substituted during generalization

**Why hole 4 appears in inner lambda's type**:
- Inner lambda's body uses outer lambda's parameter
- So inner lambda's type depends on outer lambda's parameter type (hole 4)
- When inner lambda generalizes, it doesn't know about hole 4 (created in outer context)
- So hole 4 remains unsolved in inner lambda's type

**Why hole 4 is not substituted**:
- Outer lambda creates substitution: `[(4, 0), (5, 1)]` (hole → HVar index)
- Outer lambda calls `subst_value_with_hole_vars(subst, body_ty_shifted)`
- But `body_ty_shifted` has already been shifted, and hole 4 might not be in it

**The Real Bug**: We're shifting BEFORE generalizing, but the shift doesn't add hole 4 to the body type—it just adjusts existing HVar indices. Hole 4 is in the body type (from inner lambda's use of outer parameter), but it's not being substituted.

### The Fix

The issue is that `subst_value_with_hole_vars` is being called on `body_ty_shifted`, but hole 4 might not be in `body_ty_shifted` if it was "hidden" in the inner lambda's context.

**Solution**: Don't shift before generalizing. Instead:
1. Collect holes from `body_ty` (unshifted)
2. Create substitution for ALL holes (including hole 4)
3. Apply substitution to `body_ty`
4. Then shift the result for the outer context

Or better: **Require type annotations for lambda parameters** (Option 1).

## Recommendation

### Immediate Fix (Option 3)

Fix the generalization to properly handle holes from outer contexts:

```gleam
// Don't shift before generalizing
let body_ty_unshifted = body_ty  // Use unshifted type

// Collect holes from unshifted type
let codomain_holes = free_holes_in_value(s.sub, body_ty_unshifted)

// Generalize with unshifted type
let #(generalized_implicit, generalized_t1, generalized_t2) =
  generalize_holes(holes_to_generalize, implicit, t1_hole, body_ty_unshifted, ...)

// Then shift the result
let generalized_t2_shifted = shift_hvar_in_value(generalized_t2, num_new_implicit)
```

### Long-Term Solution (Option 1 + Option 4)

1. **Require type annotations for lambda parameters** in function definitions
2. **Implement bidirectional type checking** for better inference in expressions
3. **Use constraint-based inference** for simple cases (like ML)

This gives us:
- Soundness (no incorrect type assignments)
- Completeness (where inference is decidable)
- Good usability (annotations only where needed)

---

## Implementation Plan

### Phase 1: Immediate Fix

1. Remove the premature shift in `infer(Lam)`
2. Apply shift AFTER generalization
3. Test with prelude bool module
4. Verify all tests pass

### Phase 2: Require Annotations

1. Make return type annotations required for function definitions
2. Update error messages to be helpful
3. Update documentation
4. Test with all examples

### Phase 3: Bidirectional Checking

1. Add `check` mode to type checker
2. Use `check` for lambdas with expected types
3. Use `infer` for lambdas without expected types (with annotation requirement)
4. Test comprehensively

---

## Related Documents

- **[24-lambda-inference-root-cause.md](24-lambda-inference-root-cause.md)** - Previous analysis
- **[23-lambda-inference-de-bruijn-fix.md](23-lambda-inference-de-bruijn-fix.md)** - De Bruijn fix attempt
- **[22-lambda-inference-fix-attempt-2.md](22-lambda-inference-fix-attempt-2.md)** - Attempt 2
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Final analysis
