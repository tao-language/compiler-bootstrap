# Comprehensive Analysis of Remaining 5 Test Failures

**Date**: April 6, 2026
**Status**: 445 passed, 4 failures
**Commit**: Pending — infer(Let) fix

---

## Executive Summary

**Root cause found and fixed**: The `infer(Let)` case corrupted the vars stack by updating the wrong De Bruijn position.

| Metric | Before Fix | After Fix |
|--------|-----------|-----------|
| Passing | 444 | **445** |
| Failures | 5 | 4 |
| Fixed | — | `three_fn_chain_xref_test` |

### Remaining 4 Pre-Existing Failures

| Test | Status | Root Cause |
|------|--------|------------|
| `three_match_expressions_no_conflict_test` | FAIL | Match motive InfiniteType (separate bug) |
| `match_different_result_types_test` | FAIL | Match motive InfiniteType (separate bug) |
| `match_different_types_test` | FAIL | Match motive InfiniteType (separate bug) |
| `lib_prelude_bool_module_test` | FAIL | Match motive InfiniteType (separate bug) |

All 4 remaining failures are the **same pre-existing match motive bug** — not related to the De Bruijn index fix.

---

## Root Cause: `infer(Let)` Corrupts vars Stack

### The Bug

In `src/core/infer.gleam`, the `infer(Let)` case:

```gleam
ast.Let(name, value, body, span) -> {
  let #(hole_ty, s) = new_hole(s)
  let #(_fresh, s) = def_var(s, name, hole_ty)   // ← Position 0 = name
  let s1 = state.State(..s, level: s.level + 1)
  let #(val_val, val_ty, s2) = infer(s1, value)   // ← check(Lam) prepends params!
  // BUG: update_last_var_type updates position 0, which is now the innermost param
  let s2 = state.State(..s2, vars: update_last_var_type(s2.vars, val_ty))
  ...
}
```

### Concrete Trace

For `Let("not", Fix("not", Ann(Lam("b", Bool, body), Bool→Bool)), rest)`:

```
After def_var("not"):  vars = [("not", HVar(0), hole_ty), ...original]
After infer(Fix):      vars = [("b", HVar(2), Bool), ("not", HVar(0), hole_ty), ...original]
                         ↑ position 0 is "b", NOT "not"
update_last_var_type:  vars = [("b", HVar(2), Bool→Bool), ("not", HVar(0), hole_ty), ...original]
                         ↑ WRONG entry updated          ↑ NOT updated — stays as hole!
```

The Let-bound "not" keeps its hole type. When other functions reference "not", they see a hole, not `Bool → Bool`.

### The Fix

Save `s.vars` immediately after `def_var` (where position 0 IS the Let-bound name). After `infer(value)`, restore saved vars, updating position 0's type:

```gleam
ast.Let(name, value, body, span) -> {
  let #(hole_ty, s) = new_hole(s)
  let #(_fresh, s) = def_var(s, name, hole_ty)
  let saved_vars = s.vars  // Position 0 = Let-bound name (def_var always prepends)
  let s1 = state.State(..s, level: s.level + 1)
  let #(val_val, val_ty, s2) = infer(s1, value)
  // Restore: discard temp vars from infer(value), restore saved state with updated type
  let restored_vars = case saved_vars {
    [#(n, #(val, _old_ty)), ..rest] -> [#(n, #(val, val_ty)), ..rest]
    [] -> []
  }
  let s2 = state.State(..s2, vars: restored_vars)
  let #(body_val, body_ty, s3) = infer(s2, body)
  let s4 = state.State(..s3, level: s3.level - 1)
  #(body_val, body_ty, s4)
}
```

This uses **De Bruijn position** (position 0 = most recently prepended = the name bound by def_var), not name lookup.

### Why This Is Correct

1. `def_var` always prepends at position 0
2. After `def_var(name, ...)`, position 0 IS the Let-bound name
3. We save this exact state
4. After `infer(value)`, inner bindings are at positions 0, 1, ... pushing the name down
5. We restore to the saved state (position 0 = name), updating only the type
6. This correctly updates the Let-bound name's type using its De Bruijn position

---

## Implementation

### Files Changed

| File | Change |
|------|--------|
| `src/core/infer.gleam` | Fix `infer(Let)`: save/restore vars stack |
| `src/core/ast.gleam` | Add `ast.Let` constructor (from previous work) |
| `src/tao/desugar.gleam` | Convert `CoreApp(CoreLam, CoreFix)` → `ast.Let` |
| `src/core/subst.gleam` | Add `ast.Let` handling |
| `src/core/generalize.gleam` | Add `ast.Let` handling |
| `src/core/syntax.gleam` | Add `ast.Let` handling |
| `src/core/eval.gleam` | Add `ast.Let` handling |
| `src/core/unify.gleam` | Add `ast.Let` handling |
| `test/core/fix_test.gleam` | Update tests for sequential Lam structure |
| `test/core/debruijn_level_test.gleam` | Update tests for sequential Lam structure |

### Key Design Decisions

1. **De Bruijn position, not name lookup**: The fix uses position 0 (where def_var prepends), not string comparison. This is fundamental to how De Bruijn indices work.

2. **Save/restore pattern**: Save the vars state right after def_var, then restore after value inference. This correctly discards temporary bindings created during value inference.

3. **ast.Let vs App(Lam, Fix)**: The desugaring produces `ast.Let` which has clear sequential binding semantics, avoiding the Pi-layer pollution of `App(Lam, ...)`.

---

## The Match Motive Bug (Separate, Unfixed)

The 4 remaining failures all involve `InfiniteType` errors in match expressions. These tests were added to track match motive hole conflicts and have been failing since their addition. This is a **separate bug** unrelated to the De Bruijn index issue fixed here.
