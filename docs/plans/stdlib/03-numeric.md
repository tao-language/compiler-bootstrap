# Numeric Hierarchy Specification

> **Goal**: Type-safe numeric operations via overloading
> **Status**: 📋 **Planned**
> **Date**: March 2026

---

## Status

### What's Pending

- 📋 `Num` type class (Add, Sub, Mul)
- 📋 `Fractional` type class (Div)
- 📋 `Comparable` type class
- 📋 `math/int` module
- 📋 `math/float` module

### Related

- See **[01-overview.md](./01-overview.md)** for standard library overview
- See **[02-prelude.md](./02-prelude.md)** for Prelude
- See **[../tao/10-overloading.md](../tao/10-overloading.md)** for overloading

---

## Type Class Hierarchy

```
Num
├── I32
├── I64
├── F32
└── F64

Fractional : Num
├── F32
└── F64

Comparable
├── I32
├── I64
├── F32
├── F64
└── String
```

---

## Num Type Class

### Definition

```tao
// Numeric operations via overloading
fn (+)(a: I32, b: I32) -> I32 { /* builtin */ }
fn (+)(a: F64, b: F64) -> F64 { /* builtin */ }

fn (-)(a: I32, b: I32) -> I32 { /* builtin */ }
fn (-)(a: F64, b: F64) -> F64 { /* builtin */ }

fn (*)(a: I32, b: I32) -> I32 { /* builtin */ }
fn (*)(a: F64, b: F64) -> F64 { /* builtin */ }

fn negate(a: I32) -> I32 { -a }
fn negate(a: F64) -> F64 { -a }
```

### Generic Functions

```tao
// Works for any numeric type
fn add<T>(a: T, b: T) -> T { a + b }
fn sub<T>(a: T, b: T) -> T { a - b }
fn mul<T>(a: T, b: T) -> T { a * b }
fn negate<T>(a: T) -> T { -a }

// Sum a list
fn sum<T: Num>(xs: List(T)) -> T {
  list.fold(fn(acc, x) { acc + x }, T(0), xs)
}

// Product of a list
fn product<T: Num>(xs: List(T)) -> T {
  list.fold(fn(acc, x) { acc * x }, T(1), xs)
}
```

---

## Fractional Type Class

### Definition

```tao
// Division for fractional types
fn (/)(a: F64, b: F64) -> F64 { /* builtin */ }

// Safe division returning Result
fn safe_div(a: F64, b: F64) -> Result(F64, String) {
  if b == 0.0 {
    Err("division by zero")
  } else {
    Ok(a / b)
  }
}
```

### Generic Functions

```tao
// Average of a list
fn average(xs: List(F64)) -> Option(F64) {
  let len = list.length(xs)
  if len == 0 {
    None
  } else {
    let sum = list.fold(fn(acc, x) { acc + x }, 0.0, xs)
    Some(sum / F64(len))
  }
}
```

---

## Comparable Type Class

### Definition

```tao
// Comparison returning Ordering
fn compare(a: I32, b: I32) -> Ordering { /* builtin */ }
fn compare(a: F64, b: F64) -> Ordering { /* builtin */ }
fn compare(a: String, b: String) -> Ordering { /* builtin */ }

// Comparison returning Bool
fn (<)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (<)(a: F64, b: F64) -> Bool { /* builtin */ }
// ... etc
```

### Generic Functions

```tao
// Minimum of two values
fn min<T: Comparable>(a: T, b: T) -> T {
  if compare(a, b) == LT {
    a
  } else {
    b
  }
}

// Maximum of two values
fn max<T: Comparable>(a: T, b: T) -> T {
  if compare(a, b) == GT {
    a
  } else {
    b
  }
}

// Clamp value to range
fn clamp<T: Comparable>(value: T, min: T, max: T) -> T {
  if value < min {
    min
  } else if value > max {
    max
  } else {
    value
  }
}
```

---

## math/int Module

```tao
// Integer-specific operations

// Absolute value
fn abs(n: I32) -> I32 {
  if n < 0 { -n } else { n }
}

// Sign (-1, 0, or 1)
fn sign(n: I32) -> I32 {
  if n < 0 { -1 }
  else if n > 0 { 1 }
  else { 0 }
}

// Power (integer exponent)
fn pow(base: I32, exp: I32) -> I32 {
  if exp < 0 {
    panic("negative exponent for integer power")
  } else if exp == 0 {
    1
  } else {
    pow_loop(base, exp, 1)
  }
}

fn pow_loop(base: I32, exp: I32, acc: I32) -> I32 {
  if exp == 0 {
    acc
  } else if exp % 2 == 0 {
    pow_loop(base * base, exp / 2, acc)
  } else {
    pow_loop(base, exp - 1, acc * base)
  }
}

// Min/max
fn min(a: I32, b: I32) -> I32 { if a < b { a } else { b } }
fn max(a: I32, b: I32) -> I32 { if a > b { a } else { b } }

// Conversion to string
fn to_string(n: I32) -> String { /* builtin */ }
```

---

## math/float Module

```tao
// Floating-point operations

// Absolute value
fn abs(n: F64) -> F64 {
  if n < 0.0 { -n } else { n }
}

// Sign (-1.0, 0.0, or 1.0)
fn sign(n: F64) -> F64 {
  if n < 0.0 { -1.0 }
  else if n > 0.0 { 1.0 }
  else { 0.0 }
}

// Power (floating-point exponent)
fn pow(base: F64, exp: F64) -> F64 { /* builtin */ }

// Square root
fn sqrt(n: F64) -> F64 { /* builtin */ }

// Min/max
fn min(a: F64, b: F64) -> F64 { if a < b { a } else { b } }
fn max(a: F64, b: F64) -> F64 { if a > b { a } else { b } }

// Floor/ceil
fn floor(n: F64) -> I32 { /* builtin */ }
fn ceil(n: F64) -> I32 { /* builtin */ }

// Conversion
fn to_string(n: F64) -> String { /* builtin */ }
fn from_int(n: I32) -> F64 { /* builtin */ }
```

---

## Usage Examples

```tao
import math/int
import math/float

// Integer operations
let a = int.abs(-42)      // 42
let b = int.pow(2, 10)    // 1024
let c = int.min(10, 20)   // 10

// Float operations
let x = float.sqrt(2.0)   // 1.414...
let y = float.pow(2.0, 3.0)  // 8.0
let z = float.floor(3.14) // 3

// Generic numeric functions
let sum = sum([1, 2, 3, 4, 5])  // 15
let avg = average([1.0, 2.0, 3.0])  // Some(2.0)
```

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial specification created |
