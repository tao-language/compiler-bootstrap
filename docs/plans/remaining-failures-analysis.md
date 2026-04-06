# Comprehensive Analysis of Remaining 5 Test Failures

**Date**: April 5, 2026
**Status**: 444 passed, 5 failures
**Commit**: be30486 (TypeDecl type param fix)

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

**Passing edge cases**: single function, 2 functions without cross-reference, 2 functions with cross-reference all PASS.

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
1. Evaluates `annotation` → `domain_val` (domain of annotation = first param type)
2. `def_var(name, domain_val)` → name bound to first param type
3. `infer(body)` → `body_ty` (type of Fix = annotation type of NEXT function)
4. Creates `Pi(..., domain_val, body_ty)` = `Pi(first_param_type, next_annotation)`

For 2 functions (`not`, `double_not`):
- `double_not`: Pi(Bool, Bool→Bool) = Bool → Bool → Bool ✓ (outer Lam wraps Rcd which has Bool→Bool→Bool from Fix)
- `not`: Pi(Bool, Bool→Bool→Bool) = Bool → Bool → Bool → Bool ✗

Wait, this should fail for 2 functions too, but it passes. Let me re-check...

Actually, the issue is more nuanced. The Fix's return type depends on what `infer_fix` does:
- If Fix body is `Ann`: returns annotation type
- If Fix body is Lam: creates hole, checks Lam against hole, returns solved hole

For 2 functions, the innermost Fix's Lam creates holes for param types, unifies with constructors (Bool), returns `Pi(Bool, Bool)`. The outer sequential Lam's hole unifies with this, returning `Pi(Bool, Bool)` (correct).

For 3+ functions, the nesting causes misalignment: the Fix's solved hole gets unified with the wrong type because of how the sequential App(Lam) nesting works.

### Attempted Fixes (All Failed)

1. **param_type = None + Ann(value, annotation)**: Created 17 failures. The Ann wraps Fix but `infer_fix` checks Fix body, not Fix itself.

2. **CoreLetAnn with ast.Let**: Core AST doesn't have Let. Converting to App/Lam recreated the issue.

3. **infer_fix handles Lam specially**: Either created holes (same as before) or inferred body type (caused wrong bindings).

4. **Infer Fix body Lam type**: Bound name with inferred type, but outer Lam still added Pi layer.

### The Fundamental Issue

The sequential binding Lam (`build_sequential_loop`) adds a Pi layer for EACH function. The type-checker's `infer(Lam)` always wraps the body type in Pi. This is correct for function abstractions but wrong for sequential name bindings.

**The correct fix requires**: Either:
- A) Change the desugaring to NOT use App/Lam for sequential bindings (needs ast.Let support in core/ast)
- B) Change `infer(Lam)` to NOT add Pi layer when param_type is a Hole (risky - affects all Lam inference)
- C) Add a new core AST node for sequential bindings (e.g., `ast.SeqBind`)

**Recommendation**: Option A is cleanest. Add `ast.Let` to core/ast and modify `core_term_to_term_loop` to convert `CoreLet` to `ast.Let`. The type-checker's `infer` for `ast.Let` would:
1. Infer value type
2. Add name to env with that type  
3. Infer body type
4. Return body type (no Pi layer)

---

## Unit Tests Added

Created `test/core/multi_fn_type_test.gleam` with 5 tests:
- `single_fn_match_test` — PASS ✓
- `two_fn_no_xref_test` — PASS ✓
- `two_fn_xref_test` — PASS ✓
- `two_fn_match_xref_test` — PASS ✓
- `three_fn_chain_xref_test` — FAIL ✗

These tests demonstrate the issue clearly: everything works up to 2 functions, fails at 3+.

---

## Next Steps

1. Add `ast.Let` to `src/core/ast.gleam`
2. Update `core_term_to_term_loop` to convert `CoreLet` to `ast.Let`
3. Add `infer` and `check` cases for `ast.Let` in `src/core/infer.gleam`
4. Revert `build_sequential_loop` to use `CoreLet` instead of `App(Lam, value)`
5. Run full test suite to verify fix
