# Type Annotations and Constructor Registration Fix

> **Goal**: Properly desugar type annotations and register type definitions in Core
> **Status**: 🚧 **In Progress** - Phase 1-3 complete, Phase 4 requires lambda inference fix
> **Date**: March 2026
> **Priority**: **CRITICAL** - Affects ALL code, not just prelude

---

## Overview

**Problem**: The Tao compiler currently has issues with type annotations in function definitions due to hole ID conflicts between desugaring and type checking.

**Impact**: 
- Type annotations like `fn not(b: Bool) -> Bool` cause InfiniteType errors
- 4 test failures remain (lib_prelude_bool, nested_fn, higher_order, recursive_fn)

**Root Cause**: Holes created during desugaring have fixed IDs (like 0), while type checking creates holes with unique IDs. When both are used together, the occurs check fails.

**Solution**: 
1. Don't create holes during desugaring - use constructor environment instead
2. Fix lambda inference to properly solve all holes
3. Ensure occurs check doesn't fail for valid recursive definitions

---

## Current Status

### ✅ Phase 1: Type Annotations Infrastructure (COMPLETE)

**Completed**:
- Created `build_core_type_from_ast()` function
- Added `CorePi` constructor for Pi types
- Added `build_fn_type()` for building function types

**Issues**:
- Function type annotations with holes cause InfiniteType errors
- Currently disabled - annotations are parsed but not added

### ✅ Phase 2: Constructor Registration (COMPLETE)

**Completed**:
- Modified `process_type_definitions()` to register type constructors
- Created `state_with_constructors()` to merge constructor environments
- Updated `test_api.gleam` to use constructor environment

**Result**: Type constructors like `Bool`, `Option`, `Result` are properly registered.

### ✅ Phase 3: Type Checker Fixes (COMPLETE)

**Completed**:
- Modified `check(Fix)` to use expected type directly
- Modified `check(Lam)` to use domain type from expected VPi
- Fixed `infer(Ann)` to use `eval` for annotation types

**Issues**:
- These fixes help but don't solve the root cause
- Lambda inference still creates holes that aren't properly solved

### 🚧 Phase 4: Lambda Inference Fix (IN PROGRESS)

**TODO**:
- Fix `infer(Lam)` to properly solve all holes
- Ensure occurs check doesn't fail for valid types
- Re-enable function type annotations

---

## Implementation Progress

### Completed Changes

#### 1. Constructor Registration (`src/tao/desugar.gleam`)

```gleam
fn process_type_definitions(stmts: List(Stmt), dc: DesugarContext) -> DesugarContext {
  list.fold(stmts, dc, fn(acc_dc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _span) -> {
        // Add the type itself as a constructor
        let type_ctr = #(name, CtrDef(params: type_params, 
                                       arg_ty: Unit(...), 
                                       ret_ty: Typ(0, ...)))
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        DesugarContext(..acc_dc, ctrs: list.append(acc_dc.ctrs, [type_ctr, ..new_ctrs]))
      }
      _ -> acc_dc
    }
  })
}
```

#### 2. State Initialization (`src/tao/test_api.gleam`)

```gleam
fn state_with_constructors(dc: DesugarContext, initial: core.State) -> core.State {
  let merged_ctrs = list.append(dc.ctrs, initial.ctrs)
  core.State(..initial, ctrs: merged_ctrs)
}
```

#### 3. Type Checker Fixes (`src/core/core.gleam`)

```gleam
pub fn check(s: State, term: Term, expected_ty: Type, ty_span: Span) -> #(Value, State) {
  case term {
    Fix(name, body, span) -> {
      // Use expected type directly to avoid InfiniteType errors
      let env = get_env(s)
      let #(_fresh, s) = def_var(s, name, expected_ty)
      let #(body_val, s) = check(s, body, expected_ty, span)
      let fix_val = VFix(name, env, body)
      #(fix_val, s)
    }
    Lam(implicit, param, body, span) -> {
      case expected_ty {
        VPi(_, _, _, domain, codomain) -> {
          // Use domain type from expected VPi
          let #(_fresh, s) = def_var(s, param.0, domain)
          let codomain_val = eval(s.ffi, get_env(s), codomain)
          let #(body_val, s) = check(s, body, codomain_val, span)
          let lam_val = VLam(implicit, param.0, get_env(s), body)
          #(lam_val, s)
        }
        _ -> { /* infer and unify */ }
      }
    }
    _ -> { /* infer and unify */ }
  }
}
```

---

## Known Issues

### InfiniteType Error in Lambda Inference

**Symptom**: 
```
InfiniteType(4, VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
  VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
    VNeut(HHole(4), []), Hole(5, ...)), Hole(3, ...)))
```

**Root Cause**: 
1. Lambda inference creates holes for parameter types
2. Holes are generalized to HVar (implicit type variables)
3. But some holes remain in the body's type
4. Occurs check finds holes in types containing HVar
5. InfiniteType error

**Required Fix**:
- Fix `infer(Lam)` to properly solve all holes before generalization
- Or, don't generalize holes that appear in the body

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType in `xor` |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch) |
| `tao examples` | ⚠️ MIXED | 3 failures |
| **Total** | **520 passed, 4 failures** | Same as baseline |

---

## Related Documents

- **[20-type-annotations-root-cause.md](20-type-annotations-root-cause.md)** - Root cause analysis
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Final analysis
- **[../core/core.gleam](../../src/core/core.gleam)** - Core type checker
- **[../desugar.gleam](../../src/tao/desugar.gleam)** - Desugaring logic

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial plan created |
| March 2026 | Phase 1-3 implemented |
| March 2026 | Root cause identified: hole ID conflicts |
| March 2026 | Phase 4 in progress: lambda inference fix needed |
