# Plan: Fix Remaining 8 Test Failures

**Status:** 961 passed, 8 failures
**Goal:** 969 passed, 0 failures

---

## Summary of Failures

| # | Test | File:Line | Category | Root Cause |
|---|------|-----------|----------|------------|
| 1 | `gadt_vec_cons_type_test` | infer_test:1450 | GADT Inference | `unify_type_pattern` missing `VLitT` vs `VLitT` case |
| 2 | `gadt_vec_cons_wrong_type_test` | infer_test:1472 | GADT Inference | Same as #1 |
| 3 | `gadt_vec_cons_list_type_test` | infer_test:1521 | GADT Inference | Same as #1 |
| 4 | `gadt_expr_type_test` | infer_test:1544 | GADT Inference | `unify_type_pattern` missing `VCtr` vs `VCtr` for type values |
| 5 | `gadt_expr_add_type_test` | infer_test:1565 | GADT Inference | Same as #4 |
| 6 | `t04_type_definitions_04_gadt_expr_test` | tour_test:266 | GADT Inference | Downstream of #1-#5 |
| 7 | `unify_neutral_different_spines_test` | unify_test:224 | Unification Error Prop | `match_values` discards state when `VLit` mismatch |
| 8 | `t05_pattern_matching_08_error_pattern_test` | tour_test:316 | Unification Error Prop | Downstream of #7 |

---

## Root Cause Analysis

### Issue 1: `unify_type_pattern` Missing `VLitT` vs `VLitT` Case

**Location:** `src/core/infer.gleam` lines 1265-1270

**Problem:** The `unify_type_pattern` function handles `VLit` vs `VLit` (value literals), but not `VLitT` vs `VLitT` (type literals). This is needed for GADT self_type patterns like `#LitInt($I32)`.

**Example:**
```
self_type_val = VCtr("LitInt", VLitT(I32T))
arg_type      = VLitT(IntT)
```

The `unify_type_pattern` function should match `VLitT(I32T)` against `VLitT(IntT)` and succeed (because `IntT` matches `I32T` via `literal_type_matches_wildcard`).

**Fix:** Add a `VLitT` vs `VLitT` case to `unify_type_pattern` that uses `literal_type_matches_wildcard`.

### Issue 2: `unify_type_pattern` Missing `VCtr` vs `VCtr` for Type Values

**Location:** `src/core/infer.gleam` lines 1228-1232

**Problem:** The `unify_type_pattern` function handles `VCtr` vs `VCtr`, but only when the arguments are simple values (like `VRcd`). It doesn't handle `VCtr` vs `VCtr` when the arguments are type values (like `VLitT(I32T)`).

**Example:**
```
self_type_val = VCtr("Expr", VCtr("Expr", VLitT(I32T)))
arg_type      = VCtr("Expr", VCtr("Expr", VLitT(IntT)))
```

The `unify_type_pattern` function should recursively unify the inner `VCtr` arguments, eventually reaching `VLitT(I32T)` vs `VLitT(IntT)`, which should succeed.

**Fix:** The existing `VCtr` vs `VCtr` case already calls `unify_type_pattern(arg1, arg2, acc)`, which should recursively handle the inner arguments. But the function doesn't have a `VLitT` vs `VLitT` case, so it falls through to `_` vs `_` and returns `None`.

**Fix:** Add a `VLitT` vs `VLitT` case to `unify_type_pattern` (same as Issue 1).

### Issue 3: Unification Error Propagation

**Location:** `src/core/unify.gleam` lines 243-248

**Problem:** The `match_values` function correctly calls `add_type_mismatch_error` when `VLit(lit1) != VLit(lit2)`, but the state is not being propagated correctly through the call stack.

**Root Cause:** Looking at the code, I see that `match_values` returns `#(Value, State)`, and when an error occurs, it calls `add_type_mismatch_error(state, expected, actual)`, which returns `#(VErr, new_state)`. But the caller might be discarding the state.

**Actually, after careful analysis, I believe the issue is that the `unify_neutral_different_spines_test` is correct, and the code is working correctly. The test expects `final.errors >= 1`, and the code should produce an error. But the test is failing, which means the error is not being produced.**

**Let me re-trace the code:**

1. `unify(state, VNeut(HVar(0), [EApp(VLit(42))]), VNeut(HVar(0), [EApp(VLit(43))]), dummy_infer)`
2. `match_values(state, VNeut(HVar(0), [EApp(VLit(42))]), VNeut(HVar(0), [EApp(VLit(43))]), dummy_infer)`
3. Both are `VNeut`, so `match_neutral(state, HVar(0), [EApp(VLit(42))], HVar(0), [EApp(VLit(43))], dummy_infer)`
4. `HVar(0)` == `HVar(0)`, so `match_spines(state, [EApp(VLit(42))], [EApp(VLit(43))], dummy_infer)`
5. Both have `EApp`, so `match_values(state, VLit(42), VLit(43), dummy_infer)`
6. `VLit(42)` != `VLit(43)`, so `add_type_mismatch_error(state, VLit(42), VLit(43))`

Wait, I need to check the actual code more carefully. Let me look at the `match_values` function when handling `VLit`:

```gleam
VLit(lit1), VLit(lit2) ->
  case lit1 == lit2 {
    True -> #(expected, state)
    False -> add_type_mismatch_error(state, expected, actual)
  }
```

When `lit1 != lit2`, it calls `add_type_mismatch_error(state, expected, actual)`, which returns `#(VErr, new_state)`.

So the state should have the error. But the test is failing, which means the error is not being produced.

**Actually, I think I see the issue now.** The `match_values` function is returning `#(VErr, new_state)`, but the caller (in this case, `match_spines`) is discarding the value and only using the state. But `match_spines` returns `#(Value, State)`, so it should return both the value and the state.

Let me check the `match_spines` function:

```gleam
[EApp(arg1)], [EApp(arg2)] -> match_values(state, arg1, arg2, infer_fn)
```

This returns whatever `match_values` returns, which is `#(Value, State)`. So the state should be propagated correctly.

**OK, I think the issue is that the `unify_neutral_different_spines_test` is actually correct, and the code is working correctly. The test is failing because of a different issue.**

Let me re-read the test:

```gleam
pub fn unify_neutral_different_spines_test() {
  let state = initial_state([])
  let #( _, final) = unify(
    state,
    VNeut(HVar(0), [EApp(VLit(LitInt(42)))]),
    VNeut(HVar(0), [EApp(VLit(LitInt(43)))]),
    dummy_infer,
  )
  assert list.length(final.errors) >= 1
}
```

The test expects `final.errors >= 1`. If the code is working correctly, `final` should have at least 1 error.

But the test is failing, which means `final.errors` is 0.

**After careful analysis, I believe the issue is that the `unify` function is not correctly propagating the state.** Let me check the `unify` function:

```gleam
pub fn unify(
  state: State,
  expected: Value,
  actual: Value,
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  match_values(state, expected, actual, infer_fn)
}
```

This looks correct. It calls `match_values` and returns the result.

**Actually, I think the issue is that the `match_neutral` function is not correctly propagating the state.** Let me check the `match_neutral` function:

```gleam
fn match_neutral(
  state: State,
  head1: Head,
  spine1: List(Elim),
  head2: Head,
  spine2: List(Elim),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case head1, head2 {
    HVar(l1), HVar(l2) ->
      case l1 == l2 {
        True -> match_spines(state, spine1, spine2, infer_fn)
        False ->
          add_type_mismatch_error(
            state,
            VNeut(HVar(l1), spine1),
            VNeut(HVar(l2), spine2),
          )
      }
    ...
  }
}
```

When `l1 == l2`, it calls `match_spines(state, spine1, spine2, infer_fn)`, which returns `#(Value, State)`. So the state should be propagated correctly.

**OK, I think the issue is that the `match_spines` function is not correctly propagating the state.** Let me check the `match_spines` function:

```gleam
fn match_spines(
  state: State,
  spine1: List(Elim),
  spine2: List(Elim),
  infer_fn: fn(State, Term) -> #(Value, Value, State),
) -> #(Value, State) {
  case spine1, spine2 {
    [], [] -> #(VNeut(HVar(0), []), state)
    [EApp(arg1)], [EApp(arg2)] -> match_values(state, arg1, arg2, infer_fn)
    _, _ ->
      add_type_mismatch_error(
        state,
        VNeut(HVar(0), spine1),
        VNeut(HVar(0), spine2),
      )
  }
}
```

When `spine1 = [EApp(VLit(42))]` and `spine2 = [EApp(VLit(43))]`, it calls `match_values(state, VLit(42), VLit(43), dummy_infer)`.

This returns `#(VErr, new_state)` where `new_state` has the error. So `match_spines` returns `#(VErr, new_state)`.

Then `match_neutral` returns `#(VErr, new_state)`.

Then `match_values` (the outer one) returns `#(VErr, new_state)`.

Then `unify` returns `#(VErr, new_state)`.

So `final` should be `new_state`, which has the error.

**After careful analysis, I believe the issue is that the `unify_neutral_different_spines_test` is correct, and the code is working correctly. The test is failing because of a different issue.**

**Actually, I think I need to add some debug output to the test to see what's happening.**

But for now, let me proceed with the plan and fix the other issues first. Once the GADT inference is fixed, I can re-evaluate the unification error propagation issue.

---

## Step-by-Step Implementation Plan

### Step 1: Add `VLitT` vs `VLitT` case to `unify_type_pattern`

**File:** `src/core/infer.gleam`
**Location:** After line 1270 (after `VLit` vs `VLit` case)

**Code:**
```gleam
    // Both are literal types: use wildcard matching
    ast.VLitT(wildcard), ast.VLitT(specific) ->
      case literal_type_matches_wildcard(wildcard, specific) {
        True -> Some(acc)
        False -> None
      }
```

**Unit Test:** Add to `test/core/infer_test.gleam`:
```gleam
pub fn unify_type_pattern_vlitt_match_test() {
  // IntT should match I32T via wildcard matching
  let bindings = unify_type_pattern(VLitT(IntT), VLitT(I32T), [])
  assert bindings == Some([])
  
  // FloatT should match F64T via wildcard matching
  let bindings = unify_type_pattern(VLitT(FloatT), VLitT(F64T), [])
  assert bindings == Some([])
  
  // I32T should NOT match F64T
  let bindings = unify_type_pattern(VLitT(I32T), VLitT(F64T), [])
  assert bindings == None
}
```

### Step 2: Verify `VCtr` vs `VCtr` case works with type values

**Test:** The existing `VCtr` vs `VCtr` case already calls `unify_type_pattern(arg1, arg2, acc)`, which should recursively handle the inner arguments. Once Step 1 is complete, this should work automatically.

**Unit Test:** Add to `test/core/infer_test.gleam`:
```gleam
pub fn unify_type_pattern_vctr_nested_test() {
  // VCtr("Expr", VLitT(I32T)) should match VCtr("Expr", VLitT(IntT))
  let bindings = unify_type_pattern(
    VCtr("Expr", VLitT(I32T)),
    VCtr("Expr", VLitT(IntT)),
    [],
  )
  assert bindings == Some([])
}
```

### Step 3: Fix unification error propagation

**File:** `src/core/unify.gleam`
**Location:** Line 243-248 (VLit case)

**Issue:** After careful analysis, I believe the code is correct. The `match_values` function correctly calls `add_type_mismatch_error`, which returns `#(VErr, new_state)`. The state should be propagated correctly through the call stack.

**Debug:** Add a simple test to verify the error propagation:
```gleam
pub fn debug_unify_error_propagation_test() {
  let state = initial_state([])
  let #(result, final) = unify(
    state,
    VLit(LitInt(42)),
    VLit(LitInt(43)),
    dummy_infer,
  )
  // This should produce an error
  assert list.length(final.errors) >= 1
}
```

If this test fails, then there's a bug in the error propagation. If it passes, then the `unify_neutral_different_spines_test` is failing for a different reason.

### Step 4: Verify all GADT tests pass

**Test:** Run the GADT tests to verify they pass:
```bash
gleam test --filter "gadt"
```

If any tests fail, add debug output to see what's happening.

### Step 5: Verify tour tests pass

**Test:** Run the tour tests to verify they pass:
```bash
gleam test --filter "tour"
```

If any tests fail, add debug output to see what's happening.

---

## Verification Criteria

1. **All 14 shift tests pass** (no regression)
2. **All 5 GADT inference tests pass** (infer_test:1450, 1472, 1521, 1544, 1565)
3. **All 2 unification error propagation tests pass** (unify_test:224, tour_test:316)
4. **All 1 GADT evaluation test passes** (tour_test:266)
5. **Total: 969 passed, 0 failures**

---

## Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| `VLitT` vs `VLitT` case breaks existing code | Low | Add unit test to verify |
| `VCtr` vs `VCtr` case doesn't work with type values | Medium | Add unit test to verify |
| Unification error propagation is a deeper issue | High | Add debug test to verify |
| GADT tests have other issues | Medium | Add debug output to see what's happening |

---

## Next Steps

1. **Implement Step 1:** Add `VLitT` vs `VLitT` case to `unify_type_pattern`
2. **Implement Step 2:** Add unit tests to verify `VCtr` vs `VCtr` works with type values
3. **Implement Step 3:** Add debug test to verify unification error propagation
4. **Verify all GADT tests pass**
5. **Verify all tour tests pass**
6. **Commit all changes**
