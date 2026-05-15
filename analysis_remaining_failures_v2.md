# Comprehensive Analysis of Remaining 8 Test Failures

**Date:** 2026-05-14
**Status:** 961 passed, 8 failures

---

## Summary

All 8 remaining failures fall into **two categories**:

1. **GADT inference** (6 failures): 5 in `infer_test.gleam`, 1 in `tour_test.gleam`
2. **Unification error propagation** (2 failures): 1 in `unify_test.gleam`, 1 in `tour_test.gleam`

The GADT inference failures are the primary bottleneck. Once fixed, the tour_test GADT evaluation failure should resolve automatically.

---

## Category 1: GADT Inference Failures (6 tests)

### Root Cause

The GADT inference in `infer_ctr` is not correctly handling the unification of constructor-bound variables (like `@m`) with the argument type. The issue is in the `unify_type_pattern` function's handling of `VCtr` vs `VRcdT` and nested `VRcd` patterns.

### Detailed Analysis

#### Test 1: `gadt_vec_cons_type_test` (infer_test:1450)

**Source:**
```gleam
#Cons({x: 3.14, xs: #Nil({})})
```

**Expected:** `VCtr(_, _)` (type of Cons constructor)
**Actual:** The type inference is producing something other than `VCtr`.

**Trace:**
1. `infer` is called on `#Cons({x: 3.14, xs: #Nil({})})`
2. `infer_ctr` is called with `tag="Cons"` and `arg={x: 3.14, xs: #Nil({})}`
3. `infer` is called on `arg`, returning `(VRcd(...), VRcdT(...), state1)`
4. `lookup_constructor` finds the `Cons` constructor in the `Vec` TypeDef
5. `unify_type_pattern` is called to unify `arg_type` against `self_type_val`
6. **The unification is failing** because `self_type_val` is `VCtr("Cons", {x: ..., xs: ...})` and `arg_type` is `VRcdT(...)`

**Issue:** The `self_type_val` is a `VCtr` value (the entire constructor pattern), but the `arg_type` is a `VRcdT` type (the type of the argument). The `unify_type_pattern` function has a case for `VCtr` vs `VRcdT`, but it's extracting the `VRcd` from the `VCtr` and comparing it against the `VRcdT`. This should work, but there might be an issue with the nested `#Vec({n: m, a: a})` pattern.

#### Test 2: `gadt_vec_cons_wrong_type_test` (infer_test:1472)

**Source:**
```gleam
#Cons({x: 1, xs: #Nil({})})
```

**Expected:** `VCtr(_, _)` (type of Cons constructor, even with wrong arg type)
**Actual:** Type inference is not producing `VCtr`.

**Trace:** Same as Test 1, but with `x: 1` (Int) instead of `x: 3.14` (Float).

**Issue:** Same as Test 1. The unification should still work because `$Int` can match the hole `a`.

#### Test 3: `gadt_vec_cons_list_type_test` (infer_test:1521)

**Source:**
```gleam
#Cons({x: 1, xs: #Cons({x: 2, xs: #Nil({})})})
```

**Expected:** `VCtr(_, _)` (type of Cons constructor)
**Actual:** Type inference is not producing `VCtr`.

**Trace:** Same as Test 1, but with a nested `#Cons` in the `xs` field.

**Issue:** Same as Test 1, but with more nesting. The unification should still work because the nested `#Cons` is also a constructor application.

#### Test 4: `gadt_expr_type_test` (infer_test:1544)

**Source:**
```gleam
#LitInt(42)
```

**Expected:** `VCtr(_, _)` (type of LitInt constructor)
**Actual:** Type inference is not producing `VCtr`.

**Trace:**
1. `infer` is called on `#LitInt(42)`
2. `infer_ctr` is called with `tag="LitInt"` and `arg=42`
3. `infer` is called on `arg`, returning `(VLit(Int(42)), $Int, state1)`
4. `lookup_constructor` finds the `LitInt` constructor in the `Expr` TypeDef
5. `unify_type_pattern` is called to unify `arg_type` against `self_type_val`
6. **The unification is failing** because `self_type_val` is `VCtr("LitInt", $I32)` and `arg_type` is `$Int`

**Issue:** The `self_type_val` is `VCtr("LitInt", $I32)`, which is a `VCtr` value with a `VLitT(I32T)` argument. The `arg_type` is `$Int` (which is `VLitT(IntT)`). The `unify_type_pattern` function should match `VLitT(I32T)` against `VLitT(IntT)` and succeed (because `IntT` matches `I32T` via `literal_type_matches_wildcard`). But it's not working.

**Root Cause:** The `unify_type_pattern` function doesn't have a case for `VLitT` vs `VLitT`. It only has a case for `VLit` vs `VLit`. The `self_type_val` contains `VLitT(I32T)` (a type literal), not `VLit(Int(42))` (a value literal).

**Fix:** Add a case for `VLitT` vs `VLitT` in `unify_type_pattern` that checks if the types match (using `literal_type_matches_wildcard` or similar logic).

#### Test 5: `gadt_expr_add_type_test` (infer_test:1565)

**Source:**
```gleam
#Add({x: #LitInt(1), y: #LitInt(2)})
```

**Expected:** `VCtr(_, _)` (type of Add constructor)
**Actual:** Type inference is not producing `VCtr`.

**Trace:**
1. `infer` is called on `#Add({x: #LitInt(1), y: #LitInt(2)})`
2. `infer_ctr` is called with `tag="Add"` and `arg={x: #LitInt(1), y: #LitInt(2)}`
3. `infer` is called on `arg`, returning `(VRcd(...), VRcdT(...), state1)`
4. `lookup_constructor` finds the `Add` constructor in the `Expr` TypeDef
5. `unify_type_pattern` is called to unify `arg_type` against `self_type_val`
6. **The unification is failing** because `self_type_val` is `VCtr("Add", {x: #Expr($I32), y: #Expr($I32)})` and `arg_type` is `VRcdT(...)`

**Issue:** The `self_type_val` contains `#Expr($I32)` (a `VCtr` value), which needs to be unified against the `arg_type` field types. The `unify_type_pattern` function should handle this, but it's not working correctly.

**Root Cause:** Same as Test 4. The `unify_type_pattern` function doesn't have a case for `VCtr` vs `VCtr` when the arguments are type values (like `#Expr($I32)`).

### Summary of GADT Inference Issues

1. **`unify_type_pattern` missing `VLitT` vs `VLitT` case**: The function doesn't handle type literal matching, which is needed for GADT self_type patterns like `#LitInt($I32)`.

2. **`unify_type_pattern` missing `VCtr` vs `VCtr` case for type values**: The function doesn't handle `VCtr` vs `VCtr` when the arguments are type values (like `#Expr($I32)`).

3. **Constructor-bound variables not correctly resolved**: The `@m` variable in the self_type pattern is not being correctly unified with the argument type.

---

## Category 2: Unification Error Propagation (2 tests)

### Test 6: `unify_neutral_different_spines_test` (unify_test:224)

**Test:**
```gleam
unify(state, VNeut(HVar(0), [EApp(VLit(LitInt(42)))]), VNeut(HVar(0), [EApp(VLit(LitInt(43)))]), dummy_infer)
```

**Expected:** At least 1 error in the final state
**Actual:** No errors

**Trace:**
1. `unify` is called with two `VNeut` values
2. `match_neutral` is called to compare the heads (both are `HVar(0)`)
3. `match_spines` is called to compare the spines
4. `match_values` is called to compare `VLit(LitInt(42))` vs `VLit(LitInt(43))`
5. **The comparison should fail and produce an error**, but it's not propagating correctly

**Root Cause:** The `add_type_mismatch_error` function is creating a new state with the error, but the error is not being propagated through the call stack. The issue is likely in how `match_values` handles the error case.

### Test 7: `t04_type_definitions_04_gadt_expr_test` (tour_test:266)

**Source:** `examples/core/tour/04_type_definitions/04_gadt_expr.core`
**Expected:** `VLit(Int(3))`
**Actual:** `VCall("i32_add", [VErr(...), VErr(...)], VLitT(I32T))`

**Trace:**
1. The file evaluates `#Add({x: #LitInt(1), y: #LitInt(2)})`
2. The type inference is failing (see Test 5 above)
3. The evaluation produces `VErr` values for the arguments
4. The FFI call `%i32_add` is deferred (returns `VCall`)

**Root Cause:** This is a downstream effect of the GADT inference failure. Once the GADT inference is fixed, this test should pass.

### Test 8: `t05_pattern_matching_08_error_pattern_test` (tour_test:316)

**Source:** `examples/core/tour/05_pattern_matching/08_error_pattern.core`
**Expected:** `VLit(Int(0))`
**Actual:** Something else (likely `VErr` or `VCall`)

**Trace:**
1. The file uses a pattern matching error case
2. The evaluation is not producing the expected result

**Root Cause:** This might be a separate issue with error pattern matching, or it could be related to the unification error propagation issue.

---

## Recommended Fix Priority

### High Priority (blocks all GADT tests)

1. **Add `VLitT` vs `VLitT` case to `unify_type_pattern`**: This is needed for GADT self_type patterns like `#LitInt($I32)`.

2. **Add `VCtr` vs `VCtr` case for type values to `unify_type_pattern`**: This is needed for GADT self_type patterns like `#Expr($I32)`.

3. **Fix unification error propagation in `match_values`**: This is needed for the `unify_neutral_different_spines_test`.

### Medium Priority (downstream effects)

4. **Fix `t05_pattern_matching_08_error_pattern_test`**: Once the GADT inference and unification error propagation are fixed, this test should be re-evaluated.

### Low Priority (automatically fixed)

5. **Fix `t04_type_definitions_04_gadt_expr_test`**: This is a downstream effect of the GADT inference failure. Once the GADT inference is fixed, this test should pass.

---

## Files to Modify

1. **`src/core/infer.gleam`**: Add `VLitT` vs `VLitT` and `VCtr` vs `VCtr` cases to `unify_type_pattern`
2. **`src/core/unify.gleam`**: Fix error propagation in `match_values`
3. **`test/core/infer_test.gleam`**: Verify GADT tests after fixes
4. **`test/core/unify_test.gleam`**: Verify unification error propagation after fix
5. **`test/examples/core/tour_test.gleam`**: Verify downstream tests after fixes

---

## Key Insight

The GADT inference is failing because `unify_type_pattern` doesn't handle type literal matching (`VLitT` vs `VLitT`) or type constructor matching (`VCtr` vs `VCtr` for type values). These are essential for GADT self_type patterns like `#LitInt($I32)` and `#Expr($I32)`.

Adding these cases to `unify_type_pattern` should resolve most of the GADT inference failures. The unification error propagation issue is a separate problem that needs to be fixed independently.
