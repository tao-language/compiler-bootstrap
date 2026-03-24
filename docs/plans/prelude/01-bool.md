# Bool Implementation Plan

> **Goal**: Implement Boolean type and operations to dogfood the Tao compiler
> **Status**: 📋 **Planned** - Not started
> **Date**: March 2026
> **Priority**: High - First prelude module to implement

---

## Overview

**Bool** is the simplest prelude type, making it the ideal starting point for dogfooding the Tao compiler. It tests:
- Type definitions with constructors
- Pattern matching
- Exhaustiveness checking
- FFI builtin integration
- Basic function definitions

---

## Specification

### Type Definition

```tao
// lib/prelude/bool.tao

/// Boolean type with two constructors
type Bool = True | False
```

**Core representation**:
```
CtrDef([], Unit, Bool)  -- True
CtrDef([], Unit, Bool)  -- False
```

---

### Logical Operations

#### `not`

```tao
/// Negate a boolean value
pub fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}
```

**Type signature**: `Bool -> Bool`

**Test cases**:
- `not(True)` → `False`
- `not(False)` → `True`

---

#### `and`

```tao
/// Logical AND with short-circuit evaluation
pub fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}
```

**Type signature**: `Bool -> Bool -> Bool`

**Short-circuit behavior**: If `a` is `False`, `b` is not evaluated.

**Test cases**:
- `and(True, True)` → `True`
- `and(True, False)` → `False`
- `and(False, True)` → `False`
- `and(False, False)` → `False`

---

#### `or`

```tao
/// Logical OR with short-circuit evaluation
pub fn or(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}
```

**Type signature**: `Bool -> Bool -> Bool`

**Short-circuit behavior**: If `a` is `True`, `b` is not evaluated.

**Test cases**:
- `or(True, True)` → `True`
- `or(True, False)` → `True`
- `or(False, True)` → `True`
- `or(False, False)` → `False`

---

## Examples

### Basic Usage

```tao
// lib/prelude/bool.tao

import prelude

// Basic boolean operations
let x = True
let y = False

not(x)           // False
and(x, y)        // False
or(x, y)         // True

// Complex expressions
and(or(x, y), not(y))  // True
```

### Conditional Logic

```tao
// lib/prelude/bool.tao

import prelude

/// Return the maximum of two integers (uses comparison from numbers module)
pub fn max(a: I32, b: I32) -> I32 {
  if a > b { a } else { b }
}

/// Return the minimum of two integers
pub fn min(a: I32, b: I32) -> I32 {
  if a < b { a } else { b }
}

/// Check if a number is positive (uses comparison from numbers module)
pub fn is_positive(n: I32) -> Bool {
  n > 0
}

/// Check if a number is even (uses comparison from numbers module)
pub fn is_even(n: I32) -> Bool {
  n % 2 == 0
}
```

**Note**: Comparison operators (`>`, `<`, `==`, etc.) are defined in **[02-numbers.md](./02-numbers.md)**, not in this module.

---

## Tests (REPL-style)

```tao
// lib/prelude/bool.tao

import prelude

// ============================================================================
// NOT TESTS
// ============================================================================

> not(True)
False

> not(False)
True

// ============================================================================
// AND TESTS
// ============================================================================

> and(True, True)
True

> and(True, False)
False

> and(False, True)
False

> and(False, False)
False

// ============================================================================
// OR TESTS
// ============================================================================

> or(True, True)
True

> or(True, False)
True

> or(False, True)
True

> or(False, False)
False

// ============================================================================
// COMPLEX EXPRESSIONS
// ============================================================================

> and(or(True, False), not(False))
True

> or(and(True, False), not(False))
True

> not(not(True))
True

> not(not(not(False)))
True
```

---

## Implementation Checklist

### Core Changes (if needed)

- [ ] Verify constructor type registration works for `Bool`
- [ ] Verify pattern matching exhaustiveness checking
- [ ] Verify FFI builtin calls work from Tao

### Tao Implementation

- [ ] Create `lib/prelude/bool.tao`
- [ ] Implement `Bool` type definition
- [ ] Implement `not` function
- [ ] Implement `and` function
- [ ] Implement `or` function
- [ ] Add REPL-style tests

### Examples

- [ ] Add basic usage examples
- [ ] Add conditional logic examples (using comparison operators from numbers module)

### Tests

- [ ] Add `not` tests (REPL-style)
- [ ] Add `and` tests (REPL-style)
- [ ] Add `or` tests (REPL-style)
- [ ] Add complex expression tests
- [ ] Verify all tests pass

---

## Known Issues

### Wildcard Pattern Exhaustiveness 🔴

**Issue**: Wildcard patterns (`_`) may not be recognized as exhaustive.

**Relevance to Bool**: Not directly affected - `Bool` pattern matching uses explicit constructors (`True`, `False`), not wildcards.

**Workaround**: N/A for Bool

**Fix**: See **[../core/18-exhaustiveness-wildcard-bug.md](../core/18-exhaustiveness-wildcard-bug.md)**

---

## Success Criteria

The Bool module is complete when:

1. ✅ `lib/prelude/bool.tao` compiles without errors
2. ✅ All logical operations type-check correctly
3. ✅ Example programs run successfully
4. ✅ All REPL-style tests pass
5. ✅ Error messages are clear and actionable

---

## Next Steps

After completing Bool:

1. **Document issues** - Add any compiler bugs found to this file
2. **Move to Numbers** - Start implementing `lib/prelude/numbers.tao`
3. **Update README** - Mark Bool as complete in **[README.md](./README.md)**

---

## Related Documents

- **[README.md](./README.md)** - Prelude implementation overview
- **[02-numbers.md](./02-numbers.md)** - Numbers and comparison operators
- **[../core/18-exhaustiveness-wildcard-bug.md](../core/18-exhaustiveness-wildcard-bug.md)** - Wildcard pattern bug
- **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)** - Operator overloading design

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial Bool implementation plan created |
| March 2026 | Removed comparison operators (moved to 02-numbers.md) |
| March 2026 | Updated to REPL-style tests in same file |
