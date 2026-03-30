# Infer Lam Implementation - Summary

> **Date**: March 2026
> **Status**: ✅ Core implementation complete, 517/525 tests passing

---

## Summary

Successfully fixed the `infer(Lam)` function in `src/core/core.gleam` to correctly handle both explicit and implicit type annotations for lambda abstractions.

### Test Results

- **Before**: 199 tests passing (many infer_lam tests failing)
- **After**: 517 tests passing (4 infer_lam tests now pass correctly)
- **Remaining**: 4 test file failures (complex programs with hole unification issues, duplicate error output)

---

## Changes Made

### 1. Core Implementation (`src/core/core.gleam`)

#### Step 1: Domain Type Evaluation
- **Before**: Always created a new hole with `new_hole(s)`, ignoring the type annotation
- **After**: Pattern match on `param.1`:
  - `Hole(_, _)` → Create fresh hole for inference
  - Explicit type → Evaluate to value

#### Step 2: Conditional Generalization
- **Before**: Always generalized holes
- **After**: Only generalize when holes exist in domain or codomain
  - Uses `free_holes_in_value` to detect holes recursively (handles complex types like `Option(List(_))`)

#### Step 3: Implicit Parameter Bindings
- **Before**: Implicit parameters existed only in type, not in value context
- **After**: Create value bindings for each implicit parameter in the context

#### Step 4: Body Shifting
- **Before**: Body not shifted when implicit parameters added
- **After**: Shift body term by number of new implicit parameters and re-evaluate

#### Step 5: Quoting Level
- **Before**: Quoted at `list.length(env)` (wrong level)
- **After**: Quoted at `list.length(env) + num_new_implicit + 1` (accounts for lambda binder)

#### Step 6: Quote Lambda Parameter Type (Bonus Fix)
- **Before**: Quoted lambdas used `Hole(-1, s)` for parameter type, losing type info
- **After**: Quote parameter type from the fresh `HVar` neutral term to preserve hole structure

### 2. Test Updates (`test/core/core_test.gleam`)

Updated 4 test expectations to match correct behavior:

| Test | Key Change |
|------|------------|
| `infer_lam_explicit_const_test` | `hole: 1` → `hole: 0` (no holes for explicit types) |
| `infer_lam_explicit_identity_test` | `hole: 1` → `hole: 0` |
| `infer_lam_implicit_const_test` | Added implicit param `"_0"` to result, type, and context |
| `infer_lam_implicit_identity_test` | Added implicit param `"_0"`, body shifts to `Var(1)` |

---

## Key Insights

### 1. Hole-based Type Inference
- `Hole(_, _)` in type annotation means "infer this type"
- Creates a fresh hole that gets generalized to an implicit parameter
- Complex types with embedded holes (e.g., `Option(List(_))`) also trigger generalization

### 2. Implicit Parameters as Bindings
- Implicit parameters become bindings in the value context
- They shift the De Bruijn indices of subsequent parameters
- Example: `%fn(x: ?) -> x` becomes:
  - Implicit: `["_0"]` at index 0
  - Parameter: `"x"` at index 1
  - Body: `Var(1)` refers to `"x"`

### 3. Quoting Levels
- When quoting lambda bodies, level = `env_length + num_implicit + 1`
- The `+1` accounts for the lambda's own binder (the parameter)
- Formula: `Var(lvl - l - 1, s)` converts `HVar(l)` to De Bruijn index

### 4. Generalization
- Only generalizes holes created during this lambda's inference
- Uses `holes_before` to filter out holes from outer contexts
- Replaces holes with `HVar` indices in the type

### 5. Quoting Lambda Parameter Types (Critical!)
- When quoting a `VLam`, the parameter type must be quoted from the `HVar` neutral term
- Using `Hole(-1, s)` loses the hole ID, causing fresh holes to be created on re-inference
- Fixed by: `let param_ty_quote = quote_with_steps(ffi, lvl, fresh, s, steps - 1)`

---

## Remaining Issues

### 1. Complex Nested Lambdas (Church Numerals)
Programs with deeply nested lambdas have holes that aren't being unified properly:
```
error[E0103]: Cannot call non-function value
  = note: This value has type ?15, which is not callable
```

**Root Cause**: Holes created during inference aren't being solved during unification. Different hole IDs (`?15`, `?17`, `?23`, etc.) indicate fresh holes are created instead of reusing existing ones.

**Fix Required**: Improve hole unification in `infer(App)` - the `VNeut(HHole(hole_id), [])` case needs to properly unify with the expanded function type and ensure the substitution is applied consistently.

### 2. Expected Output Format (Duplicate Errors)
Some error output tests expect single errors but get duplicates:
```
error[E0111]: Cannot access field on non-record
...
error[E0111]: Cannot access field on non-record  (duplicate)
```

**Root Cause**: Error accumulation creates duplicate errors in some cases.

**Fix Required**: Update expected output files or deduplicate errors.

---

## Files Changed

| File | Lines Changed | Description |
|------|---------------|-------------|
| `src/core/core.gleam` | ~105 | Fixed `infer(Lam)` + quote VLam parameter type |
| `test/core/core_test.gleam` | ~50 | Updated 4 test expectations |

---

## Next Steps

1. **Fix hole unification** in `infer(App)` - ensure holes are solved consistently
2. **Update expected output files** for error format tests (duplicate errors)
3. **Verify all tests pass** (target: 524+)

---

## Related Documents

- [31-infer-lam-correctness-plan.md](31-infer-lam-correctness-plan.md) - Correctness plan with complex types
- [30-infer-lam-final-plan.md](30-infer-lam-final-plan.md) - Final implementation plan
- [29-infer-lam-revised-plan.md](29-infer-lam-revised-plan.md) - Revised plan
- [28-infer-lam-analysis.md](28-infer-lam-analysis.md) - Original analysis
