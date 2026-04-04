# Bool Module Type-Checking Analysis

## Executive Summary

The `lib/prelude/bool.tao` module fails type-checking with 4 errors:
- `VarUndefined(11)` - De Bruijn index 11 out of bounds
- `VarUndefined(15)` - De Bruijn index 15 out of bounds  
- `InfiniteType(0)` (x2) - Hole 0 unified with itself (infinite type)

**Three root causes have been identified and fixed** (commits 2951504, 244e190):
1. ✅ Unification performance (occurs check traversal) - 52s → 2s
2. ✅ Nullary constructor `arg_ty` type mismatch - eliminated `TypeMismatch(VTyp(0), VUnit)` errors
3. ✅ Missing annotated types + type exclusion from public_names - eliminated `VErr` domain errors

**One root cause remains unfixed**:
- ❌ De Bruijn index accumulation in `local_scope` across module statements

---

## Detailed Analysis

### Root Cause #1: Unification Performance (FIXED ✅)

**Commit**: 2951504

**Problem**: The `occurs` check in `src/core/unify.gleam` traversed entire environments for `VPi`/`VFix`/`VLam` values, causing exponential blowup.

```gleam
// BEFORE: Traverses entire environment
ast.VLam(_, _, env, body) ->
  occurs(sub, id, env_value) || occurs_in_term(sub, id, body)
```

**Fix**: Only check explicit type components:

```gleam
// AFTER: Skip environment traversal
ast.VLam(_, _, _, _) -> False
ast.VPi(_, _, _, in_val, out_term) ->
  occurs(sub, id, in_val) || occurs_in_term(id, out_term)
ast.VFix(_, _, _) -> False
```

**Result**: bool.tao type-checking: 52s → 2s

**Tests**: `test/core/unify_test.gleam`

---

### Root Cause #2: Nullary Constructor `arg_ty` Type Mismatch (FIXED ✅)

**Commit**: 244e190

**Problem**: For nullary constructors (`True`, `False`), the `arg_ty` field was set to `core_ast.Unit(...)` which **evaluates** to `VUnit`. But during type-checking, the inferred type of the implicit `Unit` argument is `VTyp(0)` (the type universe). The `check_type` comparison fails because `VTyp(0) ≠ VUnit`.

```
Type mismatch:
  Expected: VTyp(0)    // Type of the Unit term
  Got:      VUnit      // The Unit term itself
```

**Location**: `src/tao/desugar.gleam`

```gleam
// BEFORE: arg_ty = Unit (evaluates to VUnit - the VALUE)
[] -> core_ast.Unit(Span("unit", 0, 0, 0, 0))

// AFTER: arg_ty = Typ(0) (evaluates to VTyp(0) - the TYPE)
[] -> core_ast.Typ(0, Span("unit", 0, 0, 0, 0))
```

**Also fixed**: The type constructor itself (line 214) had the same issue.

**Result**: Eliminated 5 `TypeMismatch(VTyp(0), VUnit)` errors

**Why this is correct**: In dependent type theory, `Unit` is a term whose type is `Typ(0)`. The `arg_ty` field of `CtrDef` represents the **expected type** of the constructor's argument, not the argument value itself. For nullary constructors, the implicit Unit argument has type `Typ(0)`.

---

### Root Cause #3: Missing Annotated Types + Type Exclusion (FIXED ✅)

**Commit**: 244e190 (two parts)

**Part A: Missing annotated types**

**Problem**: `desugar_module` called `core_term_to_term(core_term)` with no `annotated_types`, so module-level lambda parameter types were holes instead of resolved types. This caused `VErr` in Pi type domains.

```gleam
// BEFORE: No annotated types passed
let term = core_term_to_term(core_term)  // annotated_types = []

// AFTER: Pass collected annotated types
let term = core_term_to_term_with_annotations(core_term, dc1.annotated_types)
```

**Fix**: Added `core_term_to_term_with_annotations()` function and updated all call sites in `desugar_module_with_ctrs`.

**Part B: Type names in public_names**

**Problem**: `get_public_names` included `StmtType` names (like "Bool") in the return record. Since there's no corresponding `CoreLet("Bool", ...)` binding, the `CoreVar("Bool", span)` falls back to `ast.Var(0, span)`, referencing the wrong variable.

```gleam
// BEFORE: Types included
fn get_public_names_helper(body, acc) {
  case get_stmt_name(stmt) {
    Some(name) -> [..., name, ..]  // Includes "Bool"!
  }
}

// AFTER: Types excluded
fn get_public_names_helper(body, acc) {
  case stmt {
    StmtType(_, _, _, _) -> get_public_names_helper(rest, acc)  // Skip types
    _ -> { ... }
  }
}
```

**Result**: Eliminated `VPi(..., VErr, ...)` domain errors and incorrect variable references.

---

### Root Cause #4: De Bruijn Index Accumulation (UNFIXED ❌)

**Status**: Identified, understood, NOT fixed

**Problem**: During desugaring, `DesugarContext.local_scope` accumulates ALL names across module statements:

```
After "not(b)":       local_scope = ["not", "b"]
After "and(a, b)":    local_scope = ["and", "a", "b", "not", "b"]
After "or(a, b)":     local_scope = ["or", "a", "b", "and", "a", "b", "not", "b"]
After "xor(a, b)":    local_scope = 14+ elements
After "implies(a, b)": local_scope = 17+ elements
```

Variable references use `lookup_var(dc, name)` which returns De Bruijn indices against this accumulated scope. For example, in `implies`, `lookup_var("not")` returns index 11.

During type-checking, the context is built from nested lambdas:
```
(λnot. (λand. (λor. (λxor. (λimplies. return_record) fix_implies) fix_xor) fix_or) fix_and) fix_not
```

The context only has 5 elements (`[implies, xor, or, and, not]`), so index 11 is out of bounds → `VarUndefined(11)`.

**Why simple fixes don't work**:

1. **Reset scope between statements**: Broke type resolution and increased errors. The `local_scope` is used not just for variable lookup but also for type resolution and expression desugaring within nested structures.

2. **Use named variables instead of indices**: Would require changes to the core type-checker to support module-level named bindings.

3. **Compute indices relative to each function's scope only**: The De Bruijn indices for cross-function references (e.g., `xor` calling `not`) need to match the type-checker's context, which includes ALL outer lambdas.

**Deep architectural issue**: The De Bruijn indices are computed during desugaring against `local_scope`, but the type-checker's context is built from the nested lambda structure. These two don't align when:
- Functions reference OTHER functions (cross-references)
- Functions have multiple parameters
- There are 3+ functions in the module

**Current behavior**:
- 1-2 functions: Works (indices happen to align)
- 3 functions: May fail depending on complexity
- 4+ functions: Consistently fails

**Test**: `test/tao/debruijn_scope_test.gleam` (two_functions passes, four_functions disabled)

**Potential fix approaches**:

| Approach | Complexity | Risk | Description |
|----------|------------|------|-------------|
| **A. Reset scope + fix type resolution** | Medium | Medium | Reset `local_scope` between statements, fix any type resolution that depends on accumulated scope |
| **B. Use named variables for module-level refs** | High | High | Change desugaring to use named variables for cross-function refs, add module-level context support to type-checker |
| **C. Compute correct De Bruijn indices** | High | Medium | Compute indices against the expected type-checker context, not the desugaring scope |
| **D. Flatten module structure** | Medium | Medium | Use a different representation for module-level bindings that doesn't rely on nested lambdas |

**Recommendation**: Approach C - compute correct De Bruijn indices. The type-checker's context structure is well-defined (nested lambdas), so we can compute indices that match.

---

## Current Test Results

```
415 passed, 1 failure
```

The single failure is `lib_prelude_bool_module_test` with 4 errors.

## Error Count Progression

| Stage | Errors | Description |
|-------|--------|-------------|
| Before any fixes | 18+ | TypeMismatch(VTyp(0), VUnit), VPi(...VErr...), InfiniteType, VarUndefined |
| After fix #1 (unification) | 18+ | Same errors, but type-checking now completes in 2s instead of timing out |
| After fixes #2, #3 (desugaring) | 4 | VarUndefined(11), VarUndefined(15), InfiniteType(0) x2 |

## Files Modified

| File | Change | Commit |
|------|--------|--------|
| `src/core/unify.gleam` | Optimize occurs check | 2951504 |
| `src/tao/desugar.gleam` | Fix arg_ty, annotated_types, type exclusion | 244e190 |
| `src/tao/ast.gleam` | Skip types in get_public_names | 244e190 |
| `test/tao/debruijn_scope_test.gleam` | New test file | c0c3dd1 |

## References

- `test/core/infinite_type_debug_test.gleam` - Debug tests for InfiniteType errors
- `test/lib/prelude/bool_test.gleam` - The failing test
- `lib/prelude/bool.tao` - The module being type-checked
- `docs/lessons-learned.md` - Development principles
