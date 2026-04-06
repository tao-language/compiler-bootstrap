# Comprehensive Analysis of Remaining 5 Test Failures

**Date**: April 6, 2026
**Status**: 444 passed, 5 failures
**Commit**: 91c126d (multi-function type tests)

---

## Executive Summary

All 5 failures trace to **one root cause**: Multi-function cross-reference type mismatch in the desugaring of sequential function definitions.

| Test | Status | Details |
|------|--------|---------|
| `lib_prelude_bool_module_test` | FAIL | TypeMismatch + NotAFunction |
| `three_match_expressions_no_conflict_test` | FAIL | TypeMismatch |
| `match_different_result_types_test` | FAIL | AssertionError |
| `match_different_types_test` | FAIL | AssertionError |
| `three_fn_chain_xref_test` | FAIL | New test - 3+ functions fail |

**Passing edge cases**: single function, 2 functions (same or different annotations) all PASS.

---

## Root Cause Analysis

### The Desugaring Structure

For a module with N functions, `build_sequential_loop` creates:

```
App(Lam(f1, Some(ann1), App(Lam(f2, Some(ann2), ... App(Lam(fN, Some(annN), Rcd([f1..fN])), Fix(fN, bodyN)) ...), Fix(f2, body2))), Fix(f1, body1))
```

Each function is wrapped as `App(Lam(name, Some(annotation), body), Fix(name, inner_body))`.

### Why This Creates Extra Pi Layers

When `infer` processes `Lam(name, Some(annotation), body)`:
1. Evaluates `annotation` → `domain_val`
2. `def_var(name, domain_val)` → name bound to domain value
3. `infer(body)` → `body_ty`
4. Creates `Pi(..., domain_val, body_ty)`

**The annotation is the FULL function type** (e.g., `Pi(Bool, Pi(Bool, Bool))` for `fn or(a: Bool, b: Bool) -> Bool`).

But `infer(Lam)` uses this as the DOMAIN, creating:
```
Pi(Pi(Bool, Pi(Bool, Bool)), body_ty)
```

This is WRONG. The Pi's domain should be just `Bool`, not the full function type.

### Why 2 Functions Work But 3+ Fail

For 2 functions where BOTH have the SAME annotation type (e.g., `Pi(Bool, Bool)`):
- The Pi's domain = annotation
- The Fix's type = annotation
- Unification: annotation = annotation ✓
- Result: body_ty (correct)

For 3+ functions with DIFFERENT annotation types:
- The nesting creates `Pi(ann1, Pi(ann2, Rcd_type))`
- The body_ty from the inner App is `Rcd_type`
- The outer Pi is `Pi(ann1, Rcd_type)`
- But ann1 may differ from what the unification expects
- The hole generalization in `infer(Lam)` creates additional complexity

### Deep Dive Findings (April 6, 2026)

After extensive analysis, the following was discovered:

1. **The Pi layer is semantically wrong**: The sequential Lam shouldn't create a Pi type. It's just a binding mechanism, not a function abstraction.

2. **Hole generalization compounds the issue**: Each `infer(Lam)` generalizes holes at its lambda depth. With nested Lams, holes from different depths interact incorrectly.

3. **The Fix's annotation IS used correctly**: `infer_fix` binds the name to the annotation type and checks the lambda body against it. The Fix returns the correct type.

4. **The problem is ONLY with the outer Lam wrapper**: It creates `Pi(annotation, body_ty)` instead of just `body_ty`.

### Attempted Fixes (All Failed)

| Approach | Result | Why It Failed |
|----------|--------|---------------|
| `param_type = None` | 7 failures | Holes don't unify correctly across nested Apps |
| Extract domain from annotation | 8 failures | App requires arg_ty = domain, but arg_ty = full annotation ≠ domain |
| `param_type = unique hole` | Same/worse | Still creates Pi(hole, body) which is wrong |
| Skip Lam entirely | Breaks everything | Name not bound, Fix body can't reference it |
| Add `ast.Let` (rejected by user) | N/A | User wants App(Lam, _) fixed, not new AST node |
| `infer(Lam)` detect sequential bindings | Syntax errors | Broke case expression structure |

### The Fundamental Issue

The `App(Lam(name, ann, body), value)` structure is designed for function application, not sequential name binding. The Lam's purpose is to create a Pi type (function abstraction), but we're using it as a binding mechanism.

**Correct semantics for sequential binding**:
1. Evaluate value (Fix)
2. Bind name to value's type
3. Continue with body
4. Return body's type (NO Pi wrapper)

**Current semantics via App(Lam, Fix)**:
1. Create Lam(name, ann, body) → Pi(ann, body_ty)
2. Evaluate Fix → ann
3. Apply: check ann = ann, return body_ty
4. Result is body_ty (correct) BUT the Pi(ann, _) is created along the way

The Pi creation is the issue. It pollutes the type environment and interacts badly with hole generalization.

---

## Unit Tests

Created `test/core/multi_fn_type_test.gleam` with 5 tests:
- `single_fn_match_test` — PASS ✓
- `two_fn_no_xref_test` — PASS ✓
- `two_fn_xref_test` — PASS ✓
- `two_fn_match_xref_test` — PASS ✓
- `three_fn_chain_xref_test` — FAIL ✗

These tests demonstrate the issue clearly: everything works up to 2 functions, fails at 3+.

---

## Potential Fixes (Not Yet Implemented)

### Option A: Change desugaring structure
Instead of `App(Lam(name, ann, body), Fix(name))`, use a structure that doesn't create Pi layers:
- Use `Ann(Fix(name, body), ann)` directly
- Or nest the Fixes: `Fix(f1, Fix(f2, Fix(f3, Rcd)))`

### Option B: Change `infer(Lam)` for sequential bindings
Detect when Lam is used as a sequential binding (param_type is a Pi type) and skip Pi creation.

### Option C: Add `ast.Let` (rejected)
The cleanest solution but user rejected adding new AST nodes.

### Option D: Fix hole generalization
The issue might be in how holes are generalized across nested Lams. Fix the generalization logic.

---

## Next Steps

1. Investigate Option A: Try restructuring to avoid App(Lam, ...) entirely
2. Or Option B: Carefully modify infer(Lam) to detect sequential bindings
3. Test thoroughly with the multi_fn_type_test suite
4. Verify all 444 existing tests still pass
