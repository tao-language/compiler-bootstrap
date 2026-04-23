# Tao Desugar Migration Plan

## Overview

**File:** `src/tao/desugar.gleam` (2,494 lines, 94 functions)

**Current State:** Uses `core/core.Term` directly via import

**Target State:** Use `core/ast.Term` from new modular structure

## Key Insight: CoreTerm Wrapper Pattern

The desugarer uses a **wrapper pattern**:

```gleam
// Internal wrapper type (lines 56-117)
pub type CoreTerm {
  CoreVar(name: String, span: Span)
  CoreCall(name: String, args: List(CoreTerm), span: Span)
  CoreLam(param: String, body: CoreTerm, span: Span)
  CoreApp(fun: CoreTerm, arg: CoreTerm, span: Span)
  CoreRcd(fields: List(#(String, CoreTerm)), span: Span)
  CoreDot(record: CoreTerm, field: String, span: Span)
  // ... etc
}

// Conversion function (lines 2306-2458)
pub fn core_term_to_term(term: CoreTerm) -> Term {
  core_term_to_term_loop(term, [])
}
```

This is **GOOD NEWS**: Most of the desugarer works with `CoreTerm`, not `core/core.Term` directly!

## Import Analysis

### Current Import (line 48):
```gleam
import core/core.{
  type Term, type Literal as CoreLiteral, type LiteralType, 
  I32T, I64T, F32T, F64T, 
  type Pattern as CorePattern, type Case as CoreCaseType, 
  type CtrDef, CtrDef, type CtrEnv, 
  Err, Var, Rcd, Dot, Lit, LitT, Unit, Call, Lam, App, Typ, I32, F64, 
  Match as CoreMatch, Case, Fix, 
  PAny, PAs, PLit as PPlit, PRcd, PCtr as PPCtr, PUnit, PTyp, PLitT, Hole, Ctr, Ann, Pi
}
```

### Target Import:
```gleam
import core/ast as ast
import core/state as state
```

## Migration Strategy

### Phase 1: Update Import (5 minutes)

Replace the `core/core` import with:
```gleam
import core/ast as ast
```

### Phase 2: Fix CoreTerm Type Definition (10 minutes)

The `CoreTerm` type itself doesn't need changes - it's independent.

However, `CoreCaseType` currently uses `core/core.Case`:
```gleam
// Line 97
CoreMatchCore(arg: CoreTerm, motive: CoreTerm, cases: List(CoreCaseType), span: Span)
```

Change `type Case as CoreCaseType` to use `ast.Case`.

### Phase 3: Fix core_term_to_term_loop (30 minutes)

This is the **main conversion function** (lines 2306-2458). It converts `CoreTerm` → `Term`.

**Changes needed:**

| Old Constructor | New Constructor | Notes |
|----------------|-----------------|-------|
| `Var(index, span)` | `ast.Var(index, span)` | Direct replacement |
| `Rcd(fields, span)` | `ast.Rcd(fields, span)` | Direct replacement |
| `Dot(arg, field, span)` | `ast.Dot(arg, field, span)` | Direct replacement |
| `Lit(value, span)` | `ast.Lit(value, span)` | Direct replacement |
| `LitT(typ, span)` | `ast.LitT(typ, span)` | Direct replacement |
| `Unit(span)` | `ast.Unit(span)` | Direct replacement |
| `Call(name, args, span)` | `ast.Call(name, args, span)` | Direct replacement |
| `Lam(implicit, param, body, span)` | `ast.Lam(implicit, param, body, span)` | Note: param is `#(String, Term)` |
| `App(fun, implicit, arg, span)` | `ast.App(fun, implicit, arg, span)` | Direct replacement |
| `Typ(universe, span)` | `ast.Typ(universe, span)` | Direct replacement |
| `Match(arg, motive, cases, span)` | `ast.Match(arg, motive, cases, span)` | Direct replacement |
| `Case(pattern, body, guard, span)` | `ast.Case(pattern, body, guard, span)` | Use `ast.Case` |
| `Fix(name, body, span)` | `ast.Fix(name, body, span)` | Direct replacement |
| `Hole(id, span)` | `ast.Hole(id, span)` | Direct replacement |
| `Ctr(tag, arg, span)` | `ast.Ctr(tag, arg, span)` | Direct replacement |
| `Ann(term, typ, span)` | `ast.Ann(term, typ, span)` | Direct replacement |
| `Pi(implicit, name, in_term, out_term, span)` | `ast.Pi(implicit, name, in_term, out_term, span)` | Direct replacement |
| `Err(message, span)` | `ast.Err(message, span)` | Use `ast.Err` (not `state.Error`) |

**Special attention:**
- `ast.Lam` param is `#(String, Term)` - may need to create a hole for the type
- `ast.Case` uses `option.Option(ast.Term)` for guard

### Phase 4: Fix Literal Type Conversions (10 minutes)

Lines 262-280 convert constructor fields to types:

```gleam
fn constructor_field_to_type(field: ConstructorField) -> Term {
  case field {
    NamedField(_, typ) => type_ast_to_core(typ)
    UnnamedField(typ) => type_ast_to_core(typ)
  }
}
```

These use `type_ast_to_core` which returns `Term` - needs to return `ast.Term`.

### Phase 5: Fix Type AST Conversion (20 minutes)

Lines 281-350: `type_ast_to_core` and related functions

```gleam
fn type_ast_to_core(t: TypeAst) -> Term {
  case t {
    TVar(name, span) => Var(0, span)  // <- needs ast. prefix
    TApp(name, args, span) => { ... }
    // ... etc
  }
}
```

All `Term` constructors need `ast.` prefix.

### Phase 6: Fix Pattern Conversion (20 minutes)

The desugarer converts tao patterns to core patterns:

```gleam
fn pattern_to_core(pattern: Pattern) -> CorePattern {
  case pattern {
    // ... pattern matching
  }
}
```

**Pattern constructors to fix:**
- `PAny` → `ast.PAny`
- `PAs(p, name)` → `ast.PAs(p, name)`
- `PTyp(universe)` → `ast.PTyp(universe)`
- `PLit(literal)` → `ast.PLit(literal)`
- `PLitT(typ)` → `ast.PLitT(typ)`
- `PRcd(fields)` → `ast.PRcd(fields)`
- `PCtr(tag, arg)` → `ast.PCtr(tag, arg)`
- `PUnit` → `ast.PUnit`

### Phase 7: Fix CtrDef/CtrEnv Usage (15 minutes)

Lines 308-400: Building constructor types

```gleam
fn build_constructor_type(ctr: Constructor, span: Span) -> #(Term, CtrDef) {
  // ... builds CtrDef
  let ctr_def = CtrDef(params: params, arg_ty: arg_ty, ret_ty: ret_ty)
}
```

**Changes:**
- `CtrDef` is now in `core/ast` - use `ast.CtrDef`
- `CtrEnv` is now `List(#(String, ast.CtrDef))` - use `ast.CtrEnv`

### Phase 8: Fix Literal Type Constants (5 minutes)

```gleam
// Old
I32T, I64T, F32T, F64T

// New
ast.I32T, ast.I64T, ast.F32T, ast.F64T
```

### Phase 9: Fix Literal Constructors (5 minutes)

```gleam
// Old
I32(n), F64(f)

// New
ast.I32(n), ast.F64(f)
```

### Phase 10: Test After Each Phase

Run `gleam test` after each phase to catch errors early.

## Risk Analysis

### Low Risk (Straightforward Replacements)
- ✅ Import statement
- ✅ Literal types (I32T, etc.)
- ✅ Literal constructors (I32, F64, etc.)
- ✅ Pattern constructors (PAny, PAs, etc.)
- ✅ Term constructors in core_term_to_term_loop

### Medium Risk (Need Careful Checking)
- ⚠️ `ast.Lam` param type: `#(String, Term)` - ensure holes are created correctly
- ⚠️ `ast.Case` guard type: `Option(Term)` - ensure option handling is correct
- ⚠️ `ast.CtrDef` fields: `(params, arg_ty, ret_ty)` - verify order matches

### High Risk (Complex Interactions)
- 🔴 Type AST conversion functions - many nested conversions
- 🔴 CtrDef building - complex type construction

## Testing Strategy

1. **Compile after each phase** - catch type errors early
2. **Run full test suite** - ensure no regressions
3. **Check specific examples:**
   - Function definitions
   - Pattern matching
   - Type annotations
   - Constructor definitions

## Estimated Time

| Phase | Description | Time |
|-------|-------------|------|
| 1 | Update import | 5 min |
| 2 | Fix CoreTerm type | 10 min |
| 3 | Fix core_term_to_term_loop | 30 min |
| 4 | Fix literal type conversions | 10 min |
| 5 | Fix type AST conversion | 20 min |
| 6 | Fix pattern conversion | 20 min |
| 7 | Fix CtrDef/CtrEnv | 15 min |
| 8-9 | Fix literals | 10 min |
| 10 | Testing | 30 min |
| **Total** | | **~2.5 hours** |

## Success Criteria

- ✅ All 384 tests pass
- ✅ No build warnings
- ✅ `core_term_to_term` produces valid `ast.Term`
- ✅ Type checking works correctly
- ✅ Pattern matching works correctly

## Rollback Plan

If migration fails:
```bash
git checkout src/tao/desugar.gleam
```

The file is currently stable and working. We can retry migration later.
