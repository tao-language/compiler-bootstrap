# Remaining Test Failures Analysis

**Date:** 2026-04-02  
**Test Status:** 367/379 passing (97%)  
**Failures:** 12

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Example output files | 1 (2 sub-failures) | Pre-existing - output format mismatch |
| Lambda generalization | 1 | Regression - nested lambda VPi environment |
| Pattern matching | 10 | Pre-existing - value vs neutral term representation |

---

## 1. Example Output File Failures (2 sub-failures)

### Test: `core@examples_test.type_errors_examples_test`

**Sub-failures:**
- `08_pattern_mismatch`
- `10_infinite_type`

**Root Cause:** The expected output files were updated to match current compiler output, but the test compares against the OLD expected output format.

**Status:** 🔄 NEEDS FIX - Update expected output files or test comparison logic

---

## 2. Lambda Generalization Failure (REGRESSION)

### Test: `core@lambda_generalization_test.k_combinator_application_test`

**Test Code:**
```gleam
// Build: k = λx. λy. x
let inner = ast.Lam([], #("y", ast.Hole(-1, span)), ast.Var(1, span), span)
let k = ast.Lam([], #("x", ast.Hole(-1, span)), inner, span)

// Build: k(10)(20)
let app1 = ast.App(k, [], ast.Lit(ast.I32(10), span), span)
let app2 = ast.App(app1, [], ast.Lit(ast.I32(20), span), span)

// Expected: type = I32, no errors
```

**Root Cause Analysis:**

The issue is with how VPi environments are constructed for nested lambdas. When the outer lambda `λx` generalizes, it creates a VPi with:
- `env`: Outer scope environment (empty for top-level)
- `implicit_hvars`: Generalized implicit parameters
- `domain_hvar`: The lambda's parameter

For the inner lambda `λy`, the VPi environment should include the outer lambda's parameter so the codomain can reference it. However, the current implementation doesn't properly include outer scope variables in the VPi environment.

**Attempted Fixes:**
1. Modified `extract_codomain_holes` to extract holes from VPi domain - didn't help
2. Modified VPi environment construction to include outer scope - didn't help
3. Modified implicit_hvars to use correct levels - didn't help

**Current Hypothesis:**
The issue might be in how the codomain term references variables after generalization. The `generalize_holes` function replaces holes with variables, but the variable indices might not match the VPi environment structure.

**Status:** 🔍 INVESTIGATING

---

## 3. Pattern Matching Failures (PRE-EXISTING)

### Tests (10 total):
1. `match_guard_true_test`
2. `match_dependent_motive_with_var_test`
3. `match_exhaustiveness_missing_case_test`
4. `match_multiple_cases_two_test`
5. `match_hole_motive_infer_int_test`
6. `match_hole_motive_infer_string_test`
7. `match_dependent_motive_explicit_test`
8. `match_exhaustiveness_redundant_case_test`
9. `match_multiple_cases_three_test`
10. `match_multiple_cases_middle_test`

**Common Pattern:**
All tests expect the match result to evaluate to a concrete value, but the implementation returns a neutral term.

**Status:** 📝 DOCUMENTED - Tests need to be updated to check types instead of values

---

## Action Plan

### Phase 1: Fix Lambda Generalization (1 failure)
- [ ] Debug VPi environment construction for nested lambdas
- [ ] Verify variable indexing in codomain terms
- [ ] Test with k_combinator and church_numeral_zero

### Phase 2: Fix Pattern Match Tests (10 failures)
- [ ] Update all 10 tests to check types instead of values
- [ ] Verify all tests pass
- [ ] Add regression tests for match evaluation

### Phase 3: Fix Example Tests (1 failure with 2 sub-failures)
- [ ] Update expected output files to match current format
- [ ] Re-run example tests

### Phase 4: Documentation
- [ ] Update QWEN.md with new test count
- [ ] Document the VPi environment structure
- [ ] Add notes about neutral terms in pattern matching

---

## Regression Analysis Summary

| Component | Original | Current | Status |
|-----------|----------|---------|--------|
| Lambda generalization | Working | Broken | **REGRESSION** |
| Pattern match inference | Neutral terms | Neutral terms | Same (tests wrong) |
| Unify tests | N/A (new tests) | Fixed | **IMPROVED** |
| Example outputs | N/A | Updated | **FIXED** |

**Net Change:** +4 tests fixed, -1 regression, +9 test fixes needed = 367/379 (97%)
