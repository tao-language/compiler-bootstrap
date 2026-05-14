# Comprehensive Analysis of Remaining Test Failures

## Summary

There are 7 test failures across 3 files:
- `test/core/infer_test.gleam`: 4 failures (GADT-related)
- `test/core/unify_test.gleam`: 1 failure (neutral spine matching)
- `test/examples/core/tour_test.gleam`: 2 failures (GADT expression evaluation)

## 1. infer_test.gleam:1450 - gadt_vec_cons_type_test

### Test Description
Tests GADT-style vector construction with `#Cons({x: 3.14, xs: #Nil({})})` against a `Vec` TypeDef with GADT parameters.

### Expected Behavior
The test expects the inferred type to be `VCtr(_, _)` (a constructor type).

### Actual Behavior
The inferred type is NOT a `VCtr`. Looking at the test comments:
```
Cons has args {x: 3.14, xs: #Nil({})}
x: 3.14 should match a -> a = $Float
xs: #Nil({}) should match #Vec({n: m, a: a}) -> m = 0, a = $Float
Result type: #Vec({n: %i32_add(0, 1), a: $Float}) = #Vec({n: 1, a: $Float})
```

### Root Cause
The issue is in how `infer_ctr` handles GADT-style constructor inference. The current implementation:
1. Infers the argument type
2. Looks up the constructor in the TypeDef
3. Unifies the argument with `self_type`
4. Returns the `result_type` from the TypeDef

However, the `result_type` contains GADT parameter substitutions (like `%i32_add(0, 1)`) that need to be evaluated. The current code returns the raw `result_type` Term without evaluating it to a Value.

### Fix Required
In `infer_ctr`, after unifying the argument with `self_type`, the `result_type` Term needs to be:
1. Substituted with the solved GADT bindings
2. Evaluated/inferred to get its Value form
3. Returned as the type

The current code returns `result_type_val` directly without inference.

## 2. infer_test.gleam:1472 - gadt_vec_cons_wrong_type_test

### Test Description
Similar to the above, but with a type mismatch: `#Cons({x: 1, xs: #Nil({})})` where `x: 1` is `$Int` but should match `a`.

### Expected Behavior
The test expects the inferred type to be `VCtr(_, _)`.

### Root Cause
Same as above - the `result_type` is not being evaluated to a Value.

## 3. infer_test.gleam:1544 - gadt_expr_litint_type_test

### Test Description
Tests `#LitInt(42)` against an `Expr` TypeDef with GADT literal type constraints.

### Expected Behavior
The test expects the inferred type to be `VCtr(_, _)` (specifically `#Expr($I32)`).

### Root Cause
The `infer_ctr` function needs to:
1. Match `#LitInt($I32)` self_type against the argument `42`
2. Solve for the GADT parameter `a` (which should be `$I32`)
3. Return `#Expr($I32)` as the type

The issue is that the literal type matching (`$I32` matching `42`) is not being handled correctly in the unification step.

## 4. infer_test.gleam:1565 - gadt_expr_add_type_test

### Test Description
Tests `#Add({x: #LitInt(1), y: #LitInt(2)})` against an `Expr` TypeDef.

### Expected Behavior
The test expects the inferred type to be `VCtr(_, _)` (specifically `#Expr($I32)`).

### Root Cause
Same as above - the GADT parameter inference and result type evaluation is not working correctly.

## 5. unify_test.gleam:224 - unify_neutral_different_spines_test

### Test Description
Tests that two neutral terms with different spines fail to unify:
- `VNeut(HVar(0), [EApp(VLit(LitInt(42)))]`
- `VNeut(HVar(0), [EApp(VLit(LitInt(43)))]`

### Expected Behavior
The test expects `list.length(final.errors) >= 1` (unification should fail).

### Actual Behavior
`list.length(final.errors) == 0` (unification succeeds when it should fail).

### Root Cause Analysis
Looking at the `match_neutral` and `match_spines` functions in `unify.gleam`:

1. When `HVar(l1)` and `HVar(l2)` have the same level, `match_spines` is called
2. `match_spines` calls `match_values(state, arg1, arg2, infer_fn)` for `EApp` arguments
3. `match_values` should match `VLit(lit1)` vs `VLit(lit2)` and return an error if `lit1 != lit2`

The issue is that `match_values` for the `VLit` case returns `#(expected, state)` when literals match, but the error case is not being triggered correctly.

Looking at the code:
```gleam
VLit(lit1), VLit(lit2) ->
  case lit1 == lit2 {
    True -> #(expected, state)
    False -> add_type_mismatch_error(state, expected, actual)
  }
```

This looks correct. The issue might be in how the error is propagated through the call stack.

### Debugging Steps
1. Add debug logging to `match_values` to see what's happening
2. Check if `add_type_mismatch_error` is being called
3. Verify the state is being updated correctly

## 6. tour_test.gleam:266 - t04_type_definitions_04_gadt_expr_test

### Test Description
Evaluates a GADT expression: `eval #Add({x: #LitInt(1), y: #LitInt(2)}) : $I32`

### Expected Behavior
The expected result is `VLit(Int(3))`.

### Actual Behavior
The actual result is `VCall("i32_add", [VErr(VCtr("LitInt", VLit(Int(2)))), VErr(VCtr("LitInt", VLit(Int(2))))], VLitT(I32T))`.

### Root Cause
This is a downstream effect of the GADT inference issues. The type inference is not working correctly, which causes the evaluation to fail.

The evaluation is producing `VErr(VCtr("LitInt", VLit(Int(2))))` instead of `VLit(Int(2))`, indicating that the literal value is not being extracted correctly from the constructor.

## 7. tour_test.gleam:316 - (another GADT-related test)

### Test Description
Similar to the above GADT expression test.

### Root Cause
Same as above - GADT inference and evaluation issues.

## Common Themes

All the GADT-related failures share common themes:

1. **Result Type Evaluation**: The `result_type` Term from TypeDef constructors is not being evaluated/inferred to a Value before being returned.

2. **GADT Parameter Substitution**: When GADT parameters are solved during unification, the substitutions are not being applied to the `result_type` Term.

3. **Literal Type Matching**: The matching of literal types (like `$I32`) against values (like `42`) is not working correctly in the GADT context.

4. **Error Propagation**: Errors from nested unification calls are not being propagated correctly to the top level.

## Recommended Fixes

### 1. Fix `infer_ctr` to evaluate result_type

```gleam
fn infer_ctr(
  state: state.State,
  tag: String,
  arg: ast.Term,
  span: Span,
) -> #(ast.Value, ast.Value, state.State) {
  // ... existing code ...
  
  case unified {
    Some(solved_bindings) -> {
      // Apply bindings to result_type Term
      let result_term = apply_unify_bindings_to_term(solved_bindings, result_type_val)
      // Infer the result_type Term to get its Value
      let #(result_val, result_type_val2, state2) = infer(state1, result_term)
      #(ctr_val, result_type_val2, state2)
    }
    // ...
  }
}
```

### 2. Fix `unify` error propagation

Ensure that `add_type_mismatch_error` correctly updates the state and that the error is propagated through the call stack.

### 3. Add debug logging

Add temporary debug logging to trace the execution flow and identify where things are going wrong.

## Priority Order

1. **High**: Fix `infer_ctr` to evaluate result_type (fixes 4 infer_test failures)
2. **High**: Fix GADT parameter substitution in result_type
3. **Medium**: Fix unify error propagation (fixes 1 unify_test failure)
4. **Low**: Fix downstream evaluation issues (fixes 2 tour_test failures - will be fixed by above)
