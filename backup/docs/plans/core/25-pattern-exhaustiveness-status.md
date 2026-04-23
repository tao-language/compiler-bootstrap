# Pattern Exhaustiveness - Current Status and Next Steps

> **Date**: March 2026
> **Status**: ✅ Wildcard/Variable Fixed, ⏳ Constructor Exhaustiveness Needs Type Information

---

## Summary

### Fixed ✅

1. **Wildcard patterns** (`match x { | _ -> 100 }`) - Work correctly
2. **Variable patterns** (`match x { | n -> 100 }`) - Work correctly
3. **Constructor pattern parsing** (`match opt { | Some(x) -> x | None -> 0 }`) - Parses correctly

### Remaining Issue ⏳

**Constructor pattern exhaustiveness checking** - The exhaustiveness checker reports "Pattern match not exhaustive" for `Some` + `None` patterns, even though they cover all cases of `Option`.

---

## Root Cause

The exhaustiveness checker in `core.gleam` uses `State.ctrs` to determine which constructors belong to which types. However, it needs **type information** about the scrutinee to know which constructors to check for.

### Current Flow

1. Tao code is parsed → Tao AST
2. Tao AST is desugared → Core Term
3. Core Term is type-checked with `infer(initial_state, term)`
4. During type checking, `check_exhaustiveness` is called for match expressions

### The Problem

The exhaustiveness checker has access to `s.ctrs` (constructor definitions), but it doesn't know:
1. **What type the scrutinee has** (e.g., `Option(Int)`)
2. **Which constructors belong to that type**

Without type information, the checker can't determine that `Some` + `None` covers all cases of `Option`.

---

## Required Fix: Type-Directed Exhaustiveness Checking

### Step 1: Get Scrutinee Type

During type checking of a match expression, we need to:
1. Infer the type of the scrutinee
2. Extract the type constructor (e.g., `Option` from `Option(Int)`)

### Step 2: Look Up Constructors by Type

Use the type constructor to look up all constructors for that type from `s.ctrs`.

### Step 3: Check Coverage

Compare the patterns in the match against the list of constructors for that type.

---

## Implementation Plan

### Phase 1: Extract Type from Scrutinee

**File**: `src/core/core.gleam`, `infer_match` function

When checking a match expression:
```gleam
fn infer_match(s: State, scrutinee: Term, cases: List(Case), span: Span) -> ... {
  // First, infer the type of the scrutinee
  let #(scrutinee_value, scrutinee_type, s1) = infer(s, scrutinee)
  
  // Extract the type constructor (e.g., "Option" from App(Ctr("Option"), Int))
  let type_constructor = extract_type_constructor(scrutinee_type)
  
  // Pass type information to exhaustiveness checker
  let exhaustiveness_errors = check_exhaustiveness_with_type(s1, type_constructor, cases, span)
  ...
}
```

### Phase 2: Look Up Constructors by Type

**File**: `src/core/core.gleam`, `check_exhaustiveness_with_type` function

```gleam
fn check_exhaustiveness_with_type(
  s: State,
  type_constructor: String,
  cases: List(Case),
  span: Span,
) -> List(Error) {
  // Get all constructors for this type from s.ctrs
  let constructors_for_type = get_constructors_for_type(s.ctrs, type_constructor)
  
  // Check if patterns cover all constructors
  check_coverage(constructors_for_type, cases, span)
}
```

### Phase 3: Handle Type Variables

For polymorphic types like `Option(a)`, we need to:
1. Ignore type parameters when matching constructors
2. Check that all constructors are covered regardless of type arguments

---

## Alternative: Simpler Heuristic

As a simpler first step, we could use a heuristic:

1. **Collect all constructor names** from the patterns
2. **Look up known types** that have exactly those constructors
3. **If found**, check coverage; otherwise, skip exhaustiveness checking

This would work for common types like `Option`, `Result`, `Bool`, etc.

---

## Current Workaround

For now, users can add a wildcard case:
```tao
match opt {
  | Some(x) -> x
  | None -> 0
  | _ -> panic  // Redundant but silences exhaustiveness checker
}
```

Or use `if let` style:
```tao
match opt {
  | Some(x) -> x
  | _ -> 0  // Wildcard is recognized as exhaustive
}
```

---

## Files to Modify

1. **`src/core/core.gleam`** - Add type-directed exhaustiveness checking
2. **`src/core/core.gleam`** - Add `extract_type_constructor` helper
3. **`src/core/core.gleam`** - Add `get_constructors_for_type` helper

---

## Testing Strategy

1. Test with `Option` patterns
2. Test with `Result` patterns
3. Test with `Bool` patterns
4. Test with custom types (when user-defined types are supported)
5. Test with polymorphic types

---

## Related Documents

- **[docs/plans/core/23-pattern-exhaustiveness-final-fix.md](./23-pattern-exhaustiveness-final-fix.md)** - Wildcard/variable fix
- **[docs/plans/core/24-constructor-environment-plan.md](./24-constructor-environment-plan.md)** - Constructor environment plan
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language with exhaustiveness checking
