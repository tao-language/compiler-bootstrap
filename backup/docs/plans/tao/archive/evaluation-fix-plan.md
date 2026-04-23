# Comprehensive Plan: Fix Tao Evaluation Issues

## Problem Analysis

### Current State
- 503 tests passing, 6 tests failing
- Simple expressions work: `5 + 3` → `8` ✓
- Function definitions parse correctly but don't evaluate properly
- Lambda applications return function definitions instead of results
- Recursive functions produce stuck terms

### Failing Test Analysis

#### 1. simple_fn.tao
```tao
fn add(x: I32, y: I32) -> I32 { x + y }
add(20, 22)
```
**Expected:** `42` (or stuck term showing application)
**Actual:** `%fix add = %fn(x) -> %fn(y) -> %call add(x, y)`

**Root Cause:** The module is returning the function definition instead of evaluating the application. The last statement `add(20, 22)` should be evaluated, but it's being returned as-is.

#### 2. lambda.tao
```tao
let add = fn(x, y) { x + y }
add(1, 2)
```
**Expected:** Application result
**Actual:** `%fn(y) -> %call add(y, y)` (wrong - params not captured correctly)

**Root Cause:** Lambda parameters are being captured incorrectly during desugaring.

#### 3. recursive_fn.tao
```tao
fn factorial(n: I32) -> I32 {
  match n { | 0 -> 1 | _ -> n * factorial(n - 1) }
}
factorial(5)
```
**Expected:** `120`
**Actual:** Stuck term with `%fix factorial = ...`

**Root Cause:** Fixpoint unfolding isn't working correctly - the recursive call isn't being resolved.

#### 4. nested_fn.tao
```tao
fn triple(x: I32) -> I32 { x * 3 }
let double = fn(x: I32) -> I32 { x * 2 }
let add = fn(x: I32, y: I32) -> I32 { x + y }
add(mul(double(1), 2), triple(3))
```
**Expected:** Computed result
**Actual:** Function definition

**Root Cause:** Same as #1 - last expression not being evaluated.

## Root Causes Identified

### Issue 1: Module Evaluation Returns Definition Instead of Result
**Location:** `src/tao/desugar.gleam` - `desugar_module()`

The module desugaring creates a `CoreDoBlock` with statements and a result, but the result isn't being properly threaded through the evaluation.

**Why it happens:**
1. `desugar_module()` creates `CoreDoBlock(stmts_for_block, result, module.span)`
2. The `result` term contains the last expression
3. But when converted to core/core.Term, the function bindings shadow the application

**Fix:** Ensure the CoreDoBlock properly sequences let bindings before the final expression.

### Issue 2: Lambda Parameter Scoping
**Location:** `src/tao/desugar.gleam` - `build_value_lambdas_with_scope()`

Lambda parameters are added to scope but the body desugaring doesn't see them correctly.

**Why it happens:**
1. Parameters are extracted correctly from syntax
2. But during desugaring, the scope isn't threaded properly
3. The `dc` context is updated but the body uses the wrong context

**Fix:** Verify that `build_value_lambdas_with_scope` correctly threads the updated context.

### Issue 3: Fixpoint Unfolding
**Location:** `src/core/core.gleam` - `do_app()` and `VFix` handling

Fixpoint should unfold by substituting itself into its body, but it's getting stuck.

**Why it happens:**
1. `do_app(VFix(name, env, body), arg)` should create `VLam` and apply
2. But the recursive call inside the body references the function name
3. The name lookup in the environment isn't finding the fixpoint

**Fix:** Ensure the fixpoint value is in the environment when the body is evaluated.

### Issue 4: Function Application Not Reducing
**Location:** `src/core/core.gleam` - `eval()` and `do_app()`

Applications like `add(20, 22)` aren't reducing to values.

**Why it happens:**
1. `add` evaluates to a `VFix` containing nested lambdas
2. Application should unfold the fixpoint and apply lambdas
3. But something in the environment threading is broken

**Fix:** Trace through the evaluation step by step to find where it gets stuck.

## Detailed Fix Plan

### Step 1: Fix Module Desugaring (Priority: High)
**File:** `src/tao/desugar.gleam`

The issue is that function definitions create `CoreLet` bindings, but the final application isn't properly sequenced.

**Current code:**
```gleam
let core_term = CoreDoBlock(stmts_for_block, result, module.span)
```

**Problem:** `stmts_for_block` contains the function bindings, `result` contains the application. But the application references the function name, which should be in scope from the bindings.

**Fix:** Verify that `build_sequential_term` correctly handles this case.

### Step 2: Fix Lambda Parameter Scoping (Priority: High)
**File:** `src/tao/desugar.gleam`

**Current code:**
```gleam
fn build_value_lambdas_with_scope(...) {
  case params {
    [] -> desugar_expr_core(body, dc)
    [param, ..rest] -> {
      let dc1 = add_local(dc, param.name)
      let #(inner_body, dc2) = build_value_lambdas_with_scope(rest, body, span, dc1)
      let core_lam = CoreLam(param.name, inner_body, span)
      #(core_lam, dc2)
    }
  }
}
```

**Problem:** The `dc2` returned includes all params in scope, but the `core_lam` only has `inner_body` which was desugared with the extended scope. This should be correct, but let me verify.

**Fix:** Add debugging to verify the scope is correct.

### Step 3: Fix Fixpoint Evaluation (Priority: Medium)
**File:** `src/core/core.gleam`

**Current code:**
```gleam
VFix(name, env, body) -> {
  let fix_val = VFix(name, env, body)
  let lam_val = VLam([], name, [fix_val, ..env], body)
  do_app(ffi, lam_val, arg)
}
```

**Problem:** The fixpoint adds itself to the environment, but the body expects the function name to be at a specific De Bruijn index.

**Fix:** The fixpoint should be added at index 0 (most recent), and the body should reference it correctly.

### Step 4: Debug Evaluation Pipeline (Priority: High)
Create a simple test case and trace through:
1. Parsing → AST
2. Desugaring → CoreTerm
3. Evaluation → Value
4. Quoting → Term (for display)

## Test Cases to Verify

1. **Simple application:**
   ```tao
   fn add(x: I32, y: I32) -> I32 { x + y }
   add(1, 2)
   ```
   Should evaluate to `3`.

2. **Lambda application:**
   ```tao
   fn(x: I32): I32 { x + 1 }(5)
   ```
   Should evaluate to `6`.

3. **Let binding:**
   ```tao
   let x = 5
   x + 1
   ```
   Should evaluate to `6`.

4. **Recursive function:**
   ```tao
   fn factorial(n: I32) -> I32 {
     match n { | 0 -> 1 | _ -> n * factorial(n - 1) }
   }
   factorial(3)
   ```
   Should evaluate to `6`.

## Execution Order

1. First, add debug output to trace evaluation
2. Fix the simplest case (let binding)
3. Fix lambda application
4. Fix function definition and application
5. Fix recursive functions
6. Update test expectations
7. Run all tests
