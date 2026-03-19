# Remaining Issues Analysis and Fix Plan

## Overview

This document provides a comprehensive analysis of the remaining issues in the Tao compiler and a detailed plan to fix them.

## Current Status

- **504 tests passing**
- **5 tests failing**
  - 4 pattern matching tests (hole unsolved errors)
  - 1 import test (import not being parsed/processed correctly)

## Issue 1: Import Statement Grammar Not Working

### Symptoms

```tao
import prelude/bool

True
```

Results in:
```
error[E0102]: Undefined variable
  ┌─ tao:3:1
3 │ True
  │ ^^^^
  = note: Variable at index 0 is not defined in this scope
```

### Root Cause Analysis

The import grammar rule cannot be integrated with the existing grammar system due to type mismatches:

1. **Grammar Type System**: The `alt` function expects all alternatives to return the same type
2. **Seq Returns List**: `seq([...])` returns `List(Value(a))` where `a` is the token type
3. **Function Returns Expr**: `make_import(values)` returns `Expr`, not `List(Value(a))`
4. **Type Mismatch**: Cannot reconcile `List(Value(Token))` with `Value(Expr)`

### Current State

- ✅ Import AST type defined (`Import`, `ImportModule`, `ImportAlias`, `ImportSelective`, etc.)
- ✅ `make_import` function implemented to parse import tokens
- ✅ `desugar_import` function implemented with prelude module handling
- ✅ `CoreCtr` and `CoreUnit` constructors added for algebraic data types
- ❌ Grammar rule cannot be integrated due to type system constraints

### Fix Plan

**Option A: Rewrite Grammar System** (High effort)
- Modify the grammar DSL to support heterogeneous return types
- Allow rules to return wrapped values (`AstValue(Expr)`) directly

**Option B: Manual Parsing** (Medium effort)
- Parse imports at the lexer level before grammar parsing
- Pre-process import statements and handle them separately

**Option C: Grammar Workaround** (Low effort, recommended)
- Use a simpler grammar pattern that matches the expected type
- Accept limitations in exchange for working functionality

**Recommended**: Option C for now, with Option B as a future improvement.

## Issue 2: Pattern Matching Hole Unsolved Errors

### Symptoms

Tests failing:
- `variable_pattern.tao`
- `match_guard.tao`
- `constructor_pattern.tao`
- `recursive_fn.tao`

All report "hole unsolved" errors during type checking.

### Root Cause Analysis

1. **Match Motive Hole**: When desugaring match expressions, a hole is used for the motive:
   ```gleam
   // In desugar_match:
   let motive = CoreHole(-999, span)  // Non-dependent match
   ```

2. **Unification**: During type checking, the hole should be unified with the actual result type, but the `HoleUnsolved` error is still being reported.

3. **Error Filtering**: The code in `core.gleam` has logic to filter out `HoleUnsolved` errors for solved holes, but it's not working correctly.

### Fix Plan

1. **Check hole solving**: Add debug output to see if holes are being solved during unification

2. **Fix error filtering**: The filtering logic in `core.gleam` around line 2236 needs to be reviewed:
   ```gleam
   // Filter out HoleUnsolved errors for holes that are now solved
   case error {
     HoleUnsolved(id, _) -> {
       case dict.has_key(subst, id) {
         True -> acc  // Hole is solved, filter out error
         False -> [error, ..acc]
       }
     }
     _ -> [error, ..acc]
   }
   ```

3. **Check substitution**: Ensure the substitution is being populated correctly during pattern matching

**Recommended**: 
1. First, add debug output to understand what's happening
2. Fix the error filtering logic
3. Ensure holes are being added to the substitution during unification

## Implementation Priority

1. **Fix Pattern Matching Holes** (Issue 2) - High priority
   - Add debug output to understand hole solving
   - Fix error filtering in `core.gleam`
   - Test with pattern matching examples

2. **Fix Import Grammar** (Issue 1) - Medium priority
   - Implement Option C workaround
   - Test with simple module import first
   - Then test selective imports

## Test Plan

After fixes:

1. **Import Tests**:
   ```tao
   // Simple module import
   import prelude/bool
   True
   
   // Selective import
   import prelude/bool.{True, False}
   True
   
   // Import with alias
   import prelude/bool as B
   B.True
   ```

2. **Pattern Matching Tests**:
   ```tao
   // Variable pattern
   let x = match Some(42) { | Some(n) -> n | None -> 0 }
   
   // Constructor pattern
   match x { | True -> 1 | False -> 0 }
   
   // Match with guard
   match x { | n if n > 0 -> "positive" | _ -> "non-positive" }
   ```

## Expected Outcome

After fixes:
- **509 tests passing** (all 5 currently failing tests should pass)
- Import statements work correctly for prelude modules
- Pattern matching works without false positive hole errors
