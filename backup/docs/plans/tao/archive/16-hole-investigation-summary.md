# Pattern Matching Hole Investigation Summary

## Issue

Pattern matching tests fail with "Unsolved hole" errors:
- `variable_pattern.tao`
- `match_guard.tao`
- `constructor_pattern.tao`
- `recursive_fn.tao`

Error message:
```
error[E0106]: Unsolved hole
  ┌─ tao:5:1
5 │ match x -> I32 {
  │ ^^^^^^^
  = note: Hole #-999 was not solved during type checking
```

## Root Cause

The issue is in how the match motive is handled during type checking:

1. **Desugarer creates fixed hole**: `CoreLam("_", CoreHole(-999, span), span)`
2. **Type checker expects fresh hole**: `infer_match` creates a fresh hole for the motive type
3. **Hole ID mismatch**: -999 ≠ fresh hole ID, so unification fails
4. **Lambda checking doesn't help**: `check` calls `infer` on lambdas, which doesn't unify the body with the expected return type

## Attempted Fixes

1. **Same hole ID for value and type in `infer`**: Didn't fix because hole is never unified
2. **Evaluate motive instead of checking**: Broke other functionality
3. **Use hole from motive as return type**: Still didn't fix lambda checking issue
4. **Special-case lambda checking**: Type errors due to environment/context confusion

## Recommended Fix

**Option A: Fix `check` function for lambdas**
- Add special handling when checking `Lam` against `VPi`
- Extend context with parameter
- Check body against Pi's return type (not infer)
- This ensures holes unify correctly

**Option B: Change desugarer**
- Don't use fixed hole ID (-999)
- Let type checker create and manage holes
- Simpler fix, avoids ID mismatch

## Current Status

- 504 tests passing, 5 failing
- Import infrastructure in place (AST, desugaring, CoreCtr/CoreUnit)
- Import grammar blocked by type system constraints
- Pattern matching blocked by hole unification issue

## Next Steps

1. Implement Option B (simpler): Change desugarer to not use fixed hole ID
2. Test pattern matching examples
3. If Option B doesn't work, implement Option A (fix `check` function)
4. Fix import grammar with workaround approach
