# Numbers Implementation Plan

> **Goal**: Implement numeric types and comparison operators to test operator overloading
> **Status**: 📋 **Planned** - Not started
> **Date**: March 2026
> **Priority**: High - Tests operator overloading and FFI integration

---

## Overview

**Numbers** are essential for any programming language. This plan covers:
- Numeric type definitions (`I32`, `U32`, `I64`, `U64`, `F32`, `F64`)
- Arithmetic operators (`+`, `-`, `*`, `/`, `%`, `^`)
- Comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`)
- Operator overloading mechanism

**Why this matters**: Comparison operators test that operator overloading works correctly, which is critical for user-defined types later.

---

## Numeric Types

### Type Definitions

Numeric types are **built-in primitives** in Tao (backed by Core FFI):

```tao
// lib/prelude/numbers.tao

/// 32-bit signed integer
type I32 = %prim_i32

/// 32-bit unsigned integer
type U32 = %prim_u32

/// 64-bit signed integer
type I64 = %prim_i64

/// 64-bit unsigned integer
type U64 = %prim_u64

/// 32-bit floating point
type F32 = %prim_f32

/// 64-bit floating point
type F64 = %prim_f64
```

**Note**: These are primitive types provided by Core FFI, not user-defined ADTs.

---

## Arithmetic Operators

### Addition (`+`)

```tao
// Integer addition
pub fn (+)(a: I32, b: I32) -> I32 {
  %call i32_add(a, b)
}

pub fn (+)(a: I64, b: I64) -> I64 {
  %call i64_add(a, b)
}

// Float addition
pub fn (+)(a: F32, b: F32) -> F32 {
  %call f32_add(a, b)
}

pub fn (+)(a: F64, b: F64) -> F64 {
  %call f64_add(a, b)
}
```

### Subtraction (`-`)

```tao
// Integer subtraction
pub fn (-)(a: I32, b: I32) -> I32 {
  %call i32_sub(a, b)
}

pub fn (-)(a: I64, b: I64) -> I64 {
  %call i64_sub(a, b)
}

// Float subtraction
pub fn (-)(a: F32, b: F32) -> F32 {
  %call f32_sub(a, b)
}

pub fn (-)(a: F64, b: F64) -> F64 {
  %call f64_sub(a, b)
}
```

### Multiplication (`*`)

```tao
// Integer multiplication
pub fn (*)(a: I32, b: I32) -> I32 {
  %call i32_mul(a, b)
}

pub fn (*)(a: I64, b: I64) -> I64 {
  %call i64_mul(a, b)
}

// Float multiplication
pub fn (*)(a: F32, b: F32) -> F32 {
  %call f32_mul(a, b)
}

pub fn (*)(a: F64, b: F64) -> F64 {
  %call f64_mul(a, b)
}
```

### Division (`/`)

```tao
// Integer division (truncates toward zero)
pub fn (/)(a: I32, b: I32) -> I32 {
  %call i32_div(a, b)
}

pub fn (/)(a: I64, b: I64) -> I64 {
  %call i64_div(a, b)
}

// Float division
pub fn (/)(a: F32, b: F32) -> F32 {
  %call f32_div(a, b)
}

pub fn (/)(a: F64, b: F64) -> F64 {
  %call f64_div(a, b)
}
```

### Modulo (`%`)

```tao
// Integer modulo
pub fn (%)(a: I32, b: I32) -> I32 {
  %call i32_mod(a, b)
}

pub fn (%)(a: I64, b: I64) -> I64 {
  %call i64_mod(a, b)
}
```

**Note**: Modulo is only defined for integers, not floats.

---

## Comparison Operators

### Equality (`==`)

```tao
// I32 equality
pub fn (==)(a: I32, b: I32) -> Bool {
  %call i32_eq(a, b)
}

// I64 equality
pub fn (==)(a: I64, b: I64) -> Bool {
  %call i64_eq(a, b)
}

// F32 equality
pub fn (==)(a: F32, b: F32) -> Bool {
  %call f32_eq(a, b)
}

// F64 equality
pub fn (==)(a: F64, b: F64) -> Bool {
  %call f64_eq(a, b)
}
```

### Inequality (`!=`)

```tao
// I32 inequality
pub fn (!=)(a: I32, b: I32) -> Bool {
  %call i32_ne(a, b)
}

// I64 inequality
pub fn (!=)(a: I64, b: I64) -> Bool {
  %call i64_ne(a, b)
}

// F32 inequality
pub fn (!=)(a: F32, b: F32) -> Bool {
  %call f32_ne(a, b)
}

// F64 inequality
pub fn (!=)(a: F64, b: F64) -> Bool {
  %call f64_ne(a, b)
}
```

### Less Than (`<`)

```tao
// I32 less than
pub fn (<)(a: I32, b: I32) -> Bool {
  %call i32_lt(a, b)
}

// I64 less than
pub fn (<)(a: I64, b: I64) -> Bool {
  %call i64_lt(a, b)
}

// F32 less than
pub fn (<)(a: F32, b: F32) -> Bool {
  %call f32_lt(a, b)
}

// F64 less than
pub fn (<)(a: F64, b: F64) -> Bool {
  %call f64_lt(a, b)
}
```

### Less Than or Equal (`<=`)

```tao
// I32 less than or equal
pub fn (<=)(a: I32, b: I32) -> Bool {
  %call i32_le(a, b)
}

// I64 less than or equal
pub fn (<=)(a: I64, b: I64) -> Bool {
  %call i64_le(a, b)
}

// F32 less than or equal
pub fn (<=)(a: F32, b: F32) -> Bool {
  %call f32_le(a, b)
}

// F64 less than or equal
pub fn (<=)(a: F64, b: F64) -> Bool {
  %call f64_le(a, b)
}
```

### Greater Than (`>`)

```tao
// I32 greater than
pub fn (>)(a: I32, b: I32) -> Bool {
  %call i32_gt(a, b)
}

// I64 greater than
pub fn (>)(a: I64, b: I64) -> Bool {
  %call i64_gt(a, b)
}

// F32 greater than
pub fn (>)(a: F32, b: F32) -> Bool {
  %call f32_gt(a, b)
}

// F64 greater than
pub fn (>)(a: F64, b: F64) -> Bool {
  %call f64_gt(a, b)
}
```

### Greater Than or Equal (`>=`)

```tao
// I32 greater than or equal
pub fn (>=)(a: I32, b: I32) -> Bool {
  %call i32_ge(a, b)
}

// I64 greater than or equal
pub fn (>=)(a: I64, b: I64) -> Bool {
  %call i64_ge(a, b)
}

// F32 greater than or equal
pub fn (>=)(a: F32, b: F32) -> Bool {
  %call f32_ge(a, b)
}

// F64 greater than or equal
pub fn (>=)(a: F64, b: F64) -> Bool {
  %call f64_ge(a, b)
}
```

---

## Examples and Tests

**Note**: Tao tests are REPL-style: `> expression\nresult`. Tests serve as documentation.

```tao
// lib/prelude/numbers.tao

// ============================================================================
// ARITHMETIC EXAMPLES
// ============================================================================

> 42 + 1
43

> 10 - 3
7

> 5 * 6
30

> 20 / 4
5

> 17 % 5
2

// Integer division truncates toward zero
> 7 / 2
3

// Float division
> 7.0 / 2.0
3.5

// Mixed operations with correct precedence
> 1 + 2 * 3
7

> (1 + 2) * 3
9

// ============================================================================
// COMPARISON EXAMPLES
// ============================================================================

// Equality
> 42 == 42
True

> 42 == 43
False

// Inequality
> 42 != 43
True

> 42 != 42
False

// Less than
> 42 < 43
True

> 43 < 42
False

> 42 < 42
False

// Less than or equal
> 42 <= 42
True

> 42 <= 43
True

> 43 <= 42
False

// Greater than
> 43 > 42
True

> 42 > 43
False

> 42 > 42
False

// Greater than or equal
> 42 >= 42
True

> 43 >= 42
True

> 42 >= 43
False

// ============================================================================
// NEGATIVE NUMBERS
// ============================================================================

> -5 + 3
-2

> -10 - (-5)
-5

> -3 * -4
12

// ============================================================================
// FLOAT EXAMPLES
// ============================================================================

> 3.14 + 2.86
6.0

> 10.0 / 4.0
2.5

> 3.14 == 3.14
True

> 3.14 < 3.15
True

// ============================================================================
// COMPLEX EXPRESSIONS
// ============================================================================

// Check if a number is even
> let is_even = fn(n: I32) -> Bool { n % 2 == 0 } in is_even(42)
True

> let is_even = fn(n: I32) -> Bool { n % 2 == 0 } in is_even(43)
False

// Check if a number is positive
> let is_positive = fn(n: I32) -> Bool { n > 0 } in is_positive(42)
True

> let is_positive = fn(n: I32) -> Bool { n > 0 } in is_positive(0)
False

> let is_positive = fn(n: I32) -> Bool { n > 0 } in is_positive(-5)
False

// Maximum of two numbers
> let max = fn(a: I32, b: I32) -> I32 { if a > b { a } else { b } } in max(42, 43)
43

// Minimum of two numbers
> let min = fn(a: I32, b: I32) -> I32 { if a < b { a } else { b } } in min(42, 43)
42

// Absolute value
> let abs = fn(n: I32) -> I32 { if n < 0 { -n } else { n } } in abs(-42)
42

> let abs = fn(n: I32) -> I32 { if n < 0 { -n } else { n } } in abs(42)
42

// Check if in range
> let in_range = fn(x: I32, min: I32, max: I32) -> Bool { x >= min && x <= max } in in_range(5, 1, 10)
True

> let in_range = fn(x: I32, min: I32, max: I32) -> Bool { x >= min && x <= max } in in_range(15, 1, 10)
False

// ============================================================================
// OPERATOR OVERLOADING TESTS
// ============================================================================

// Same operator works for different types
> 42 + 1
43

> 42I64 + 1I64
43I64

> 3.14 + 1.0
4.14

// Comparison works across types
> 42 == 42
True

> 42I64 == 42I64
True

> 3.14 == 3.14
True
```

---

## Implementation Checklist

### Core FFI (already available)

- [ ] Verify `i32_add`, `i32_sub`, `i32_mul`, `i32_div`, `i32_mod`
- [ ] Verify `i32_eq`, `i32_ne`, `i32_lt`, `i32_le`, `i32_gt`, `i32_ge`
- [ ] Verify same for `i64`, `f32`, `f64`

### Tao Implementation

- [ ] Create `lib/prelude/numbers.tao`
- [ ] Define numeric type aliases (`I32`, `U32`, `I64`, `U64`, `F32`, `F64`)
- [ ] Implement arithmetic operators for `I32`
- [ ] Implement arithmetic operators for `I64`
- [ ] Implement arithmetic operators for `F32`
- [ ] Implement arithmetic operators for `F64`
- [ ] Implement comparison operators for `I32`
- [ ] Implement comparison operators for `I64`
- [ ] Implement comparison operators for `F32`
- [ ] Implement comparison operators for `F64`
- [ ] Add examples and tests (REPL-style)

### Testing

- [ ] Test arithmetic operations
- [ ] Test comparison operations
- [ ] Test negative numbers
- [ ] Test float operations
- [ ] Test complex expressions
- [ ] Test operator overloading (same operator, different types)
- [ ] Verify all examples produce expected output

---

## Known Issues

### Operator Overloading Resolution 🟡

**Issue**: How does the compiler know which `+` to call for `I32` vs `I64`?

**Expected**: Type-directed resolution based on argument types.

**Mechanism**: Tao's overloading via implicit type parameters (see **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)**).

**Test**: Verify `42 + 1` resolves to `I32` addition, `42I64 + 1I64` resolves to `I64`.

---

### Float Equality 🟡

**Issue**: Float equality (`==`) may be problematic due to NaN and precision.

**Decision**: For now, use exact equality. Document that float comparison may be unreliable.

**Future**: Consider `approx_eq` function with epsilon tolerance.

---

### Integer Overflow 🔴

**Issue**: What happens on `I32.max + 1`?

**Current**: Undefined behavior (relies on Core FFI).

**Future**: Consider checked/saturating/wrapping variants:
```tao
fn add_checked(a: I32, b: I32) -> Result(I32, OverflowError)
fn add_saturating(a: I32, b: I32) -> I32
fn add_wrapping(a: I32, b: I32) -> I32
```

---

## Success Criteria

The Numbers module is complete when:

1. ✅ `lib/prelude/numbers.tao` compiles without errors
2. ✅ All arithmetic operators work for all numeric types
3. ✅ All comparison operators work for all numeric types
4. ✅ Operator overloading resolves correctly based on types
5. ✅ All examples produce expected output
6. ✅ Error messages are clear for type mismatches

---

## Related Documents

- **[README.md](./README.md)** - Prelude implementation overview
- **[01-bool.md](./01-bool.md)** - Bool implementation (uses comparison operators)
- **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)** - Operator overloading design
- **[../core/03-ffi-comptime.md](../core/03-ffi-comptime.md)** - FFI builtins

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial Numbers implementation plan created |
