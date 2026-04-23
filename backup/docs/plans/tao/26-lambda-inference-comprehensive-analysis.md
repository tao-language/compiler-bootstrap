# Lambda Inference Fix - Comprehensive Analysis

> **Date**: March 2026
> **Status**: ❌ Unresolved - Requires Fundamental Redesign

---

## Executive Summary

After extensive investigation and multiple fix attempts, the `InfiniteType` error in lambda type inference remains unresolved. The root cause is a fundamental mismatch between the hole-based inference approach and the requirements of dependently typed lambda calculus.

**Recommendation**: Require explicit type annotations for all function definitions and implement bidirectional type checking for lambda expressions.

---

## Problem Statement

The compiler produces `InfiniteType` errors when type-checking functions with nested lambdas:

```
InfiniteType(4, VPi([], "_", [HVar(1), HVar(0)], 
  VPi([], "_", [HVar(1), HVar(0)], HHole(4), Hole(5, ...)), Hole(3, ...)))
```

This error occurs in:
- `lib/prelude/bool.tao` - `xor`, `implies` functions
- `examples/tao/programs/02-functions/nested_fn.tao`
- `examples/tao/programs/02-functions/higher_order.tao`
- `examples/tao/programs/04-recursion/recursive_fn.tao`

---

## Root Cause Analysis

### The Fundamental Issue

The current lambda inference algorithm creates holes for parameter types and attempts to generalize them after inferring the body type. This approach fails for nested lambdas because:

1. **Hole Creation Order**: Inner lambda holes are created before outer lambda holes are solved
2. **Generalization Timing**: Holes are generalized before all constraints are collected
3. **Context Mismatch**: Inner lambda types reference outer lambda holes, but these holes aren't in the inner lambda's generalization scope

### Detailed Trace

For `fn xor(a: Bool, b: Bool) -> Bool { and(or(a, b), not(and(a, b))) }`:

1. **Outer Lambda (`λa`)**:
   - Creates hole 3 for result type
   - Creates hole 4 for `a`'s type
   - Adds `a : Hole(4)` to context
   - Infers inner lambda

2. **Inner Lambda (`λb`)**:
   - Creates hole 5 for `b`'s type
   - Adds `b : Hole(5)` to context
   - Infers body: `and(or(a, b), not(and(a, b))) : Bool`
   - Collects holes: `[5]` (only hole 5, not hole 4!)
   - Generalizes: `hole 5 → HVar(0)`
   - Returns type: `VPi([], "b", [], HVar(0), Bool)`

3. **Back to Outer Lambda**:
   - Receives body type: `VPi([], "b", [], HVar(0), Bool)`
   - Collects holes: `[4]` (hole 4 from domain, no holes in codomain)
   - Generalizes: `hole 4 → HVar(0)`
   - Returns type: `VPi([], "a", [], HVar(0), VPi([], "b", [], HVar(0), Bool))`

**Problem**: The inner VPi's `in_val` should be `HVar(1)` (referring to outer lambda's first implicit), but it's `HVar(0)` (referring to inner lambda's first implicit). This causes the `InfiniteType` error when the type checker tries to unify the types.

### Why Annotations Don't Help

Even with explicit type annotations (`fn xor(a: Bool, b: Bool) -> Bool`), the annotations are not being used during type checking:

1. **Desugaring**: Creates `CoreFix(name, CoreAnn(core_lam, function_type))`
2. **Conversion**: Converts to `Fix(name, Ann(core_lam, function_type))`
3. **Type Checking**: `infer(Fix)` creates a hole and checks `Ann` against the hole
4. **Pattern Match**: `infer(Fix)` checks if body is `Ann`, but the pattern match FAILS

Debug output revealed:
```
DEBUG CoreFix(xor): Converting body, body type = Ann
DEBUG CoreFix(xor): Converted body type = Ann
DEBUG Fix(f): body is Ann = False  ← Pattern match fails!
```

The `Fix` being inferred has a different name (`f` instead of `xor`), suggesting the annotation is being lost or the `Fix` is from a different context (e.g., for loop desugaring).

---

## Fix Attempts

### Attempt 1: Fix Hole Generalization

**Approach**: Always include domain hole in `holes_to_generalize`.

**Result**: ❌ Failed - Hole 4 still appears in inner VPi's `in_val`.

**Finding**: Generalization doesn't solve the fundamental context mismatch.

### Attempt 2: HVar Shifting for Nested Lambdas

**Approach**: Shift HVar indices when embedding nested lambda types in outer context.

**Result**: ❌ Failed - Shifting is applied but hole 4 still appears.

**Finding**: The hole isn't being substituted because it's not in the substitution map.

### Attempt 3: Generalize Before Shifting

**Approach**: Collect holes from unshifted type, generalize, then shift result.

**Result**: ❌ Failed - Same InfiniteType error.

**Finding**: The issue is not the order of operations, but the fundamental approach.

### Attempt 4: Use Annotation in infer(Fix)

**Approach**: Check if `Fix` body is `Ann` and use annotated type directly.

**Result**: ❌ Failed - Pattern match fails, annotation not recognized.

**Finding**: The `Fix` being inferred is not the one with the annotation (different name).

---

## Type-Theoretic Analysis

### Why Lambda Inference is Hard

In dependently typed lambda calculus, a lambda abstraction has the form:

```
λx:A. b : Πx:A. B
```

The domain `A` must be known BEFORE we can type the lambda. We cannot infer `A` from the body alone because:

1. The body might not use `x` (constant function)
2. The body might use `x` in a way that's consistent with multiple types
3. In dependent type theory, `A` can be any type, not just simple types

### Comparison with Other Type Systems

| System | Lambda Inference | Notes |
|--------|-----------------|-------|
| **Hindley-Milner** | Complete | Simple types only, no dependent types |
| **System F** | Partial | Requires type annotations for polymorphism |
| **Dependent Types (Agda, Idris, Coq)** | None | Requires explicit type annotations |

**Conclusion**: Lambda type inference is fundamentally incomplete for dependently typed languages. The only sound approach is to require explicit type annotations.

---

## Recommended Solution

### Phase 1: Require Type Annotations (Immediate)

Modify the type checker to:
1. **Require return type annotations** for all function definitions
2. **Use annotations directly** without inference
3. **Error on missing annotations** with helpful message

```gleam
// Required syntax
fn xor(a: Bool, b: Bool) -> Bool { ... }  // ✓ OK
fn xor(a, b) -> Bool { ... }  // ✗ Error: missing parameter type annotations
fn xor(a: Bool, b: Bool) { ... }  // ✗ Error: missing return type annotation
```

### Phase 2: Bidirectional Type Checking (Long-term)

Implement bidirectional type checking with two modes:
- **Check**: Verify term has expected type (for lambdas with annotations)
- **Infer**: Synthesize type from term (for applications, variables)

This allows limited inference in expressions while maintaining soundness:
```tao
// Function definition (requires annotations)
fn map(f: a -> b, xs: List(a)) -> List(b) { ... }

// Lambda in expression (can infer from context)
let result = map(fn(x) { x + 1 }, [1, 2, 3])  // f inferred as Int -> Int
```

### Phase 3: Local Type Inference (Optional)

Add local type inference for simple cases:
```tao
let x = 42  // x : Int inferred
let f = fn(a) { a }  // Error: cannot infer, requires annotation
let g = fn(a: Int) { a }  // OK: g : Int -> Int
```

---

## Implementation Plan

### Week 1: Require Annotations
- [ ] Modify parser to require return type annotations
- [ ] Modify type checker to use annotations directly
- [ ] Add helpful error messages for missing annotations
- [ ] Update all examples with explicit annotations

### Week 2: Bidirectional Checking
- [ ] Add `check` mode to type checker
- [ ] Modify `check(Lam)` to use expected VPi type
- [ ] Modify `infer(App)` to use `check` for arguments
- [ ] Test with existing examples

### Week 3: Testing and Documentation
- [ ] Write comprehensive tests for annotation requirements
- [ ] Update documentation with new syntax requirements
- [ ] Add migration guide for existing code

---

## Lessons Learned

1. **Hole-based inference is fragile**: Holes interact in complex ways with nested binders
2. **Debugging type checkers is hard**: Need better tooling for tracing type inference
3. **Type theory matters**: Understanding the theoretical foundations is essential for correct implementation
4. **Simplicity over cleverness**: Explicit annotations are simpler and more maintainable than complex inference

---

## Related Documents

- **[25-lambda-inference-type-theoretic-analysis.md](25-lambda-inference-type-theoretic-analysis.md)** - Type-theoretic foundations
- **[24-lambda-inference-root-cause.md](24-lambda-inference-root-cause.md)** - Root cause analysis
- **[23-lambda-inference-de-bruijn-fix.md](23-lambda-inference-de-bruijn-fix.md)** - De Bruijn index fix attempt
- **[22-lambda-inference-fix-attempt-2.md](22-lambda-inference-fix-attempt-2.md)** - Attempt 2 analysis
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Type annotations analysis

---

## Appendix: Test Results

| Attempt | Tests Passing | Tests Failing | Status |
|---------|--------------|---------------|--------|
| Baseline | 519 | 5 | ❌ |
| Attempt 1 | 519 | 5 | ❌ |
| Attempt 2 | 519 | 5 | ❌ |
| Attempt 3 | 519 | 5 | ❌ |
| Attempt 4 | 518 | 6 | ❌ |

**Note**: Attempt 4 introduced a new failure (08_pattern_mismatch) due to unrelated changes.
