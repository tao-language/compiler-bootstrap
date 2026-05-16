# Implicit Parameter Fix Status

## Summary

**976 passed, 6 failures** (down from 972 passed, 10 failures)

## Fixed Tests (4 new passes)
1. `infer_direct_poly_identity_int_test` - Direct application of polymorphic identity with int
2. `infer_direct_poly_identity_float_test` - Direct application with float
3. `infer_let_self_ref_test` - Let-bound polymorphic identity function
4. `t07_advanced_02_implicit_params_test` - Parser-based implicit params test

## Remaining Failures (6 tests)

### 1-4. typeof tests (infer_typeof_int_test, infer_typeof_float_test, infer_parser_typeof_int_test, infer_parser_typeof_float_test)
**Problem**: These tests expect `$fn<a: $Type>(x: a) => a` applied to `42` to return `$Int` (the type of the argument). The implicit param `a` should be unified with the argument's type during inference.

**Current behavior**: The implicit param returns `VTyp(0)` (the type's type) instead of being unified with the argument's type.

**Root cause**: The VLam case creates fresh holes for implicit params but doesn't unify them with the argument's type. The `force()` function resolves holes but the env doesn't contain the resolved value.

**Fix needed**: The VLam case needs to unify the implicit param holes with the argument's type during beta reduction, not just create fresh holes.

### 5. infer_nested_identity_param_test
**Problem**: Similar to typeof tests - let-bound polymorphic identity not resolving implicit params.

**Root cause**: Same as above - implicit param holes not being unified with argument types.

### 6. t04_type_definitions_04_gadt_expr_test
**Problem**: GADT expr test fails with `VErr` when evaluating `eval #Add({x: #LitInt(1), y: #LitInt(2)})`.

**Root cause**: The recursive `eval` function's self-reference through `$fix` is not working correctly with implicit params.

## Changes Made

### 1. `infer_lam` (src/core/infer.gleam)
- Added implicit params to state as fresh holes BEFORE lambda param
- VLam's env now includes implicit param values (not just outer scope)
- Body indices correctly reference: Var(0)..Var(n-1) = implicits, Var(n) = lambda param

### 2. `infer_app` let binding case
- Added implicit params as fresh holes to state before lambda param
- Let-bound var at index n (after n implicit params)

### 3. `infer_app` VLam case  
- Creates fresh holes for implicit params
- Extends env with implicit param values and converted_arg
- Body indices correctly reference implicit params and lambda param

### 4. `unify_infer_and_check`
- Pass state vars to `force()` so implicit param holes can be resolved

### 5. Test fixes
- Fixed `infer_poly_identity_test` and `infer_poly_nested_type_test` De Bruijn indices

## Next Steps

### Priority 1: Resolve implicit param holes to argument types
The VLam case needs to call `unify` to unify implicit param holes with the argument's type. This requires:
1. Inferring the argument's type
2. Unifying each implicit param hole with the argument's type
3. Substituting the resolved type in the body

### Priority 2: Fix GADT expr test
The GADT expr test fails because the recursive `eval` function's self-reference doesn't work with implicit params. This requires fixing the `$fix` handling to properly resolve recursive self-references.
