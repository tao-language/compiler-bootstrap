# Match Type Inference

> **Goal**: Support both explicit motives (dependent matches) and inferred motives (non-dependent matches) via unification, without filtering errors
> **Status**: ✅ **Implemented** - Unification-based hole solving working correctly
> **Date**: March 16, 2026

---

## Status

### What's Working

- ✅ Basic match type inference with explicit motives
- ✅ Hole motive detection via `VNeut(HHole(id), [])` pattern
- ✅ Unification-based hole solving through `check` and `force`
- ✅ Multi-clause matches with hole motives
- ✅ Type mismatch errors reported correctly (not hidden)
- ✅ No error filtering - holes solved naturally via unification
- ✅ **485 tests passing** (including new hole motive tests)

### What's Pending

- ⏳ Tao syntax for explicit motives (future work)
- ⏳ Dependent match examples with scrutinee-dependent result types
- ⏳ Pattern literal matching in Tao (separate issue)
- ⏳ Exhaustiveness checking for wildcard patterns (separate issue)

### Related

- See **[01-overview.md](./01-overview.md)** for core language overall status
- See **[02-syntax.md](./02-syntax.md)** for match syntax specification
- See **[../tao/03-desugaring.md](../tao/03-desugaring.md)** for Tao desugaring rules

---

## Core Principle

**Let unification do its job.** When a match has a hole motive, the type checker's unification algorithm naturally solves the hole when checking the first clause body. No special reconstruction, no error filtering.

### The Insight

In dependent type theory:
```
Γ ⊢ scrutinee : A
Γ ⊢ motive : (x : A) → Type
Γ, x : A, p : P(x) ⊢ body : motive(x)
─────────────────────────────────────────
Γ ⊢ match scrutinee ~ motive { ... } : motive(scrutinee)
```

For non-dependent matches, the motive is `fn(_: A) → R` where `R` is unknown. We represent this as a hole: `fn(_: A) → ?R`. When we check the first clause body against `?R`, unification solves `?R` automatically.

---

## Algorithm

### High-Level Flow

```
infer_match(scrutinee, motive, cases):
  1. Infer scrutinee type: (arg_val, arg_ty)
  2. Check motive type: (x : arg_ty) → Type
  3. Apply motive to scrutinee: result_ty = motive(arg_val)
  4. Case on result_ty:
     a. If hole (VNeut(HHole(id), [])):
        - Bind first pattern
        - Check guard
        - Compute branch_ty = motive(first_pat_val)  [contains hole]
        - Check first body against branch_ty  [unification solves hole!]
        - Force motive through substitution: solved_motive = force(motive)
        - Compute solved_result_ty = solved_motive(arg_val)
        - Check remaining clauses with solved_motive
        - Return (match_val, solved_result_ty, state)
     b. If concrete:
        - Check all clauses with motive
        - Return (match_val, result_ty, state)
```

### Key Operations

| Operation | Purpose | Function |
|-----------|---------|----------|
| Bind pattern | Introduce pattern variables | `bind_pattern()` |
| Check body | Unify hole with body type | `check()` → `unify()` |
| Force value | Apply substitution to holes | `force()` |
| Apply motive | Compute branch/result type | `do_app()` |

---

## Design Decisions

### 1. No Error Filtering

**Decision**: Never filter `HoleUnsolved` errors from the error list.

**Rationale**: If a hole remains unsolved after type checking, it's a real error that should be reported. Filtering hides bugs.

**Alternative Considered**: Filter the original hole ID after solving.

**Why Rejected**: 
- Masks real type errors
- Violates error accumulation principle
- Makes debugging harder

### 2. Unification-Based Solving

**Decision**: Rely on `check()` → `unify()` to solve holes naturally.

**Rationale**: The unification algorithm is designed for this. When we check a body of type `T` against an expected type `?R` (hole), unification adds `?R ↦ T` to the substitution.

**Implementation**:
```gleam
let branch_ty = do_app(s.ffi, motive_val, first_pat_val)
// branch_ty = ?R (the hole)

let #(first_body_val, s) = check(s, first_case.body, branch_ty, ...)
// check calls unify, which adds: s.sub = [..., (hole_id, body_type), ...]
```

### 3. Force After Unification

**Decision**: Use `force()` to apply the substitution to the motive value.

**Rationale**: After unification, the substitution contains the hole binding. `force()` traverses the value and replaces holes with their bound values.

**Implementation**:
```gleam
let solved_motive_val = force(s.ffi, s.sub, motive_val)
// Replaces VNeut(HHole(hole_id), []) with the solved type
```

### 4. Hole Detection Pattern

**Decision**: Detect hole motives by pattern matching on `VNeut(HHole(id), [])`.

**Rationale**: A hole motive applied to a scrutinee produces a neutral term with a hole head and empty spine.

**Pattern**:
```gleam
case result_ty {
  VNeut(HHole(hole_id), []) -> { /* hole motive */ }
  _ -> { /* concrete motive */ }
}
```

---

## Type Theory Background

### Dependent Match

```
motive : (x : A) → Type
match a : A ~ motive {
  | p1 → b1  // b1 : motive(a) where p1 matches a
  | p2 → b2  // b2 : motive(a) where p2 matches a
} : motive(a)
```

Example: Length-indexed vectors
```
motive = fn(n : Nat) → if n == 0 then Unit else Vec(n)
match xs : Vec(n) ~ motive {
  | Nil → ()           // Unit when n == 0
  | Cons(h, t) → ...   // Vec(n) when n > 0
}
```

### Non-Dependent Match

```
motive = fn(_: A) → R  // Constant function
match a : A ~ motive {
  | p1 → b1  // b1 : R
  | p2 → b2  // b2 : R
} : R
```

When `R` is unknown, we use a hole:
```
motive = fn(_: A) → ?R
```

Unification solves `?R` from the first clause.

---

## Testing Strategy

### Unit Tests (core_test.gleam)

| Test Name | Purpose | Expected Result |
|-----------|---------|-----------------|
| `infer_match_hole_int_test` | Hole motive with Int result | Hole solved to I32T, no errors |
| `infer_match_hole_i64_test` | Hole motive with I64 result | Hole solved to I64T, no errors |
| `infer_match_hole_mismatch_test` | Type mismatch between clauses | TypeMismatch error (not HoleUnsolved) |
| `infer_match_explicit_motive_test` | Explicit non-dependent motive | Works as before |
| `infer_match_dependent_motive_test` | Dependent motive with variable | Correct dependent typing |
| `infer_match_empty_hole_test` | Empty cases with hole motive | MatchMissingCase error |

### Integration Tests (pattern_match_test.gleam)

| Test Name | Purpose | Expected Result |
|-----------|---------|-----------------|
| `match_hole_motive_infer_int_test` | Multi-clause match, infer Int | Correct value and type |
| `match_hole_motive_infer_string_test` | Multi-clause match, infer I64 | Correct value and type |
| `match_dependent_motive_explicit_test` | Explicit motive | Works correctly |
| `match_dependent_motive_with_var_test` | Pattern variable in body | Variable scoping works |

### Tao Integration Tests

| File | Purpose | Status |
|------|---------|--------|
| `examples/tao/programs/03-pattern-matching/literal_pattern.tao` | Implicit motive | ⏳ Type errors (exhaustiveness) |
| `examples/tao/programs/03-pattern-matching/wildcard_pattern.tao` | Wildcard pattern | ⏳ Type errors (exhaustiveness) |

---

## Implementation Details

### Core Changes

**File**: `src/core/core.gleam`

**Function**: `infer_match/5`

**Key Changes**:
1. Remove error filtering
2. Use `force()` to solve motive after first clause
3. Verify hole is actually solved (no `HoleUnsolved` in errors)

**Before** (incorrect):
```gleam
let #(_first_body_val, inferred_result_ty, s) = infer(s, first_case.body)
let result_term = quote(s.ffi, ..., inferred_result_ty, ...)
let concrete_motive_term = Lam(..., result_term, ...)
let #(concrete_motive_val, s) = check(s, concrete_motive_term, ...)
// ... then filter errors
let s = State(..s, errors: list.filter(s.errors, ...))
```

**After** (correct):
```gleam
let branch_ty = do_app(s.ffi, motive_val, first_pat_val)
let #(first_body_val, s) = check(s, first_case.body, branch_ty, ...)
// Unification solved the hole in branch_ty

let solved_motive_val = force(s.ffi, s.sub, motive_val)
let solved_result_ty = do_app(s.ffi, solved_motive_val, arg_val)
// No error filtering needed!
```

### Tao Desugaring

**File**: `src/tao/desugar.gleam`

**Function**: `desugar_match/4`

**Current Behavior**: Creates hole motive `CoreLam("_", CoreHole(-100, span), span)`

**Future Enhancement**: Support explicit motive syntax:
```tao
match x ~ (fn(_: Int) → Int) { ... }
```

---

## Known Issues

### 1. Exhaustiveness Checking

**Issue**: Wildcard patterns not recognized as covering all cases.

**Example**:
```tao
match x {
  | _ → 100
}
```
Reports "redundant case" error.

**Root Cause**: Exhaustiveness algorithm doesn't recognize `PAny` as exhaustive.

**Tracking**: Separate issue (exhaustiveness checking).

### 2. Match Evaluation

**Issue**: Match expressions return `{}` instead of expected values.

**Example**:
```tao
match 0 { | 0 → 42 | _ → 100 }
// Expected: 42
// Actual: {}
```

**Root Cause**: Runtime evaluation of `do_match/4` not handling patterns correctly.

**Tracking**: Separate issue (runtime evaluation).

### 3. Literal Pattern Matching

**Issue**: Multi-clause matches with literal patterns have extraction issues in Tao parser.

**Tracking**: Separate issue (Tao parser).

---

## Alternatives Considered

### Alternative 1: Reconstruct Motive

**Approach**: Infer result type, then construct new motive term and re-check.

**Pros**: 
- Explicit control over motive construction
- Clear separation of inference and checking

**Cons**:
- Duplicates work (check twice)
- Loses unification benefits
- More complex code

**Decision**: Rejected in favor of unification-based approach.

### Alternative 2: Two-Pass Inference

**Approach**: First pass infers result type, second pass checks with concrete motive.

**Pros**:
- Clean separation
- Easy to understand

**Cons**:
- Two passes over clauses
- Doesn't leverage unification
- More error-prone

**Decision**: Rejected.

### Alternative 3: Error Filtering (Previous Approach)

**Approach**: Filter out `HoleUnsolved` error for the original hole ID.

**Pros**:
- Simple to implement

**Cons**:
- **Hides real errors**
- Violates error accumulation principle
- Makes debugging impossible

**Decision**: **Rejected** (fundamentally unsound).

---

## Open Questions

### 1. Dependent Match Syntax in Tao

**Question**: Should Tao support explicit motive syntax?

**Options**:
- `match x ~ motive { ... }` (explicit)
- `match x { ... }` (implicit, current)

**Recommendation**: Add explicit syntax for dependent matches, keep implicit for non-dependent.

**Tracking**: Future enhancement.

### 2. Hole ID Management

**Question**: Should Tao desugaring use negative hole IDs (current) or positive IDs from state?

**Current**: `CoreHole(-100, span)` - negative to avoid conflicts

**Alternative**: Allocate hole ID from `s.hole` counter

**Recommendation**: Keep negative IDs for desugaring, positive for type checker.

---

## Change Log

| Date | Change | Author |
|------|--------|--------|
| 2026-03-16 | Initial plan created | AI Assistant |
| 2026-03-16 | Removed error filtering from `infer_match` | AI Assistant |
| 2026-03-16 | Added `force()`-based hole solving | AI Assistant |
| 2026-03-16 | Added comprehensive tests | AI Assistant |

---

## References

- [Type Theory Documentation](../core.md)
- [Unification Algorithm](../core.md#unification)
- [Normalization by Evaluation](../core.md#normalization-by-evaluation)
- [Tao Desugaring Specification](../tao/03-desugaring.md)
