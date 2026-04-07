# Comprehensive Analysis of Remaining Test Failures

**Date**: April 6, 2026
**Status**: 446 passed, 3 failures
**Commit**: Pending — match case body environment fix

---

## Executive Summary

**Two root causes found and fixed**:

1. **`infer(Let)` vars stack corruption** (fixed) — Let-bound names kept hole types, causing 3+ function cross-reference failures.
2. **Match case body empty environment** (fixed) — Case body variables resolved to wrong bindings, causing `InfiniteType`.

| Metric | Before All Fixes | After All Fixes |
|--------|-----------------|-----------------|
| Passing | 444 | **446** |
| Failures | 5 | **3** |
| Fixed | — | `three_fn_chain_xref_test`, `three_match_expressions_no_conflict_test` |

### Remaining 3 Pre-Existing Failures

| Test | Status | Root Cause |
|------|--------|------------|
| `match_different_result_types_test` | FAIL | Match motive InfiniteType (separate bug) |
| `match_different_types_test` | FAIL | Match motive InfiniteType (separate bug) |
| `lib_prelude_bool_module_test` | FAIL | Test count mismatch (18 vs 20) |

---

## Fix 1: `infer(Let)` Corrupts vars Stack (RESOLVED)

**Bug**: `update_last_var_type(s2.vars, val_ty)` updated vars position 0 after `infer(value)`. But `check(Lam)` in `infer(Fix)` prepended parameter bindings, shifting the Let-bound name down. The name kept its hole type.

**Fix**: Save `s.vars` after `def_var`, restore after `infer(value)` with updated type. Uses De Bruijn position (def_var always prepends at 0).

---

## Fix 2: Match Case Body Empty Environment (RESOLVED)

**Bug**: `desugar_single_case` called `core_term_to_term(core_body)` with empty env `[]`. All `CoreVar(name)` defaulted to `Var(0)`. At type-checking, `Var(0)` resolved to the motive parameter `"_"` (typed as a fresh hole), making both function and argument the same hole → `InfiniteType`.

**Fix**: Keep case bodies as `CoreTerm`, convert in `core_term_to_term_loop` with correct env containing enclosing lambda/let/fix bindings.

**Implementation**:
- Added `CoreCase` type (body/guard as `CoreTerm`)
- Changed `CoreMatchCore` to use `List(CoreCase)`
- Updated `desugar_single_case`, `desugar_match_clauses_to_cases`, for/while loops
- Fixed `core_term_to_term_loop(CoreMatchCore)` to convert bodies with current env

---

## Remaining 3 Failures (Unrelated)

### `match_different_result_types_test` and `match_different_types_test`

Fail with `InfiniteType` even though case bodies are concrete constructors (no variable references). The bug is in match motive hole handling.

### `lib_prelude_bool_module_test`

Fails with `18 should equal 20` — test expectation mismatch (18 test annotations exist in bool.tao).
