# Prelude Specification

> **Goal**: Define essential types and operations auto-imported in every Tao program
> **Status**: ⏳ **In Progress** - Implementation started
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Core language support for sum types (constructors)
- ✅ Pattern matching with exhaustiveness checking
- ✅ Operator overloading via implicit arguments

### What's Pending

- 📋 `Bool` type and operations
- 📋 `Option(a)` type and operations
- 📋 `Result(a, e)` type and operations
- 📋 `Ordering` type
- 📋 Function combinators

### Related

- See **[01-overview.md](./01-overview.md)** for standard library overview
- See **[../tao/10-overloading.md](../tao/10-overloading.md)** for overloading mechanism

---

## Module Structure

```
lib/prelude/
├── prelude.core.tao   # Core prelude (auto-imported)
├── bool.core.tao      # Boolean type
├── option.core.tao    # Option type
├── result.core.tao    # Result type
└── ordering.core.tao  # Ordering type
```

**Note**: Files use `.core.tao` extension as they contain Core language syntax.

---

## Bool Type

### Definition

```tao
// Boolean type with two constructors
type Bool = True | False
```

### Operations

```tao
// Logical operations (overloaded operators)
fn (&&)(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}

fn (||)(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> True
    | False -> b
  }
}

fn not(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}

// Comparison operations returning Bool
fn (==)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (!=)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (<)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (>)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (<=)(a: I32, b: I32) -> Bool { /* builtin */ }
fn (>=)(a: I32, b: I32) -> Bool { /* builtin */ }
```

### Usage

```tao
let x = true && false  // false
let y = true || false  // true
let z = not(true)      // false

let a = (1 == 2)  // false
let b = (1 < 2)   // true
```

---

## Option Type

### Definition

```tao
// Optional value: Some(x) or None
type Option(a) = Some(a) | None
```

### Operations

```tao
// Predicates
fn is_some<T>(opt: Option(T)) -> Bool {
  match opt {
    | Some(_) -> True
    | None -> False
  }
}

fn is_none<T>(opt: Option(T)) -> Bool {
  match opt {
    | Some(_) -> False
    | None -> True
  }
}

// Extraction (partial - panics on None)
fn unwrap<T>(opt: Option(T)) -> T {
  match opt {
    | Some(x) -> x
    | None -> panic("unwrap called on None")
  }
}

// Safe extraction with default
fn unwrap_or<T>(opt: Option(T), default: T) -> T {
  match opt {
    | Some(x) -> x
    | None -> default
  }
}

// Mapping
fn map<T, U>(opt: Option(T), f: fn(T) -> U) -> Option(U) {
  match opt {
    | Some(x) -> Some(f(x))
    | None -> None
  }
}

// Flat mapping (bind)
fn and_then<T, U>(opt: Option(T), f: fn(T) -> Option(U)) -> Option(U) {
  match opt {
    | Some(x) -> f(x)
    | None -> None
  }
}

// Get value or compute default
fn unwrap_or_else<T>(opt: Option(T), f: fn() -> T) -> T {
  match opt {
    | Some(x) -> x
    | None -> f()
  }
}
```

### Usage

```tao
let x: Option(I32) = Some(42)
let y: Option(I32) = None

is_some(x)  // true
is_none(y)  // true

unwrap(x)   // 42
unwrap_or(y, 0)  // 0

map(x, fn(n) { n * 2 })  // Some(84)
and_then(x, fn(n) { if n > 0 { Some(n) } else { None } })  // Some(42)
```

---

## Result Type

### Definition

```tao
// Result with error: Ok(value) or Err(error)
type Result(a, e) = Ok(a) | Err(e)
```

### Operations

```tao
// Predicates
fn is_ok<T, E>(result: Result(T, E)) -> Bool {
  match result {
    | Ok(_) -> True
    | Err(_) -> False
  }
}

fn is_err<T, E>(result: Result(T, E)) -> Bool {
  match result {
    | Ok(_) -> False
    | Err(_) -> True
  }
}

// Extraction (partial - panics on Err)
fn unwrap<T, E>(result: Result(T, E)) -> T {
  match result {
    | Ok(x) -> x
    | Err(e) -> panic("unwrap called on Err")
  }
}

// Safe extraction with default
fn unwrap_or<T, E>(result: Result(T, E), default: T) -> T {
  match result {
    | Ok(x) -> x
    | Err(_) -> default
  }
}

// Mapping over Ok
fn map<T, E, U>(result: Result(T, E), f: fn(T) -> U) -> Result(U, E) {
  match result {
    | Ok(x) -> Ok(f(x))
    | Err(e) => Err(e)
  }
}

// Mapping over Err
fn map_err<T, E, F>(result: Result(T, E), f: fn(E) -> F) -> Result(T, F) {
  match result {
    | Ok(x) => Ok(x)
    | Err(e) => Err(f(e))
  }
}

// Flat mapping (bind)
fn and_then<T, E, U>(result: Result(T, E), f: fn(T) -> Result(U, E)) -> Result(U, E) {
  match result {
    | Ok(x) => f(x)
    | Err(e) => Err(e)
  }
}

// Convert to Option (discard error)
fn ok<T, E>(result: Result(T, E)) -> Option(T) {
  match result {
    | Ok(x) => Some(x)
    | Err(_) => None
  }
}
```

### Usage

```tao
let x: Result(I32, String) = Ok(42)
let y: Result(I32, String) = Err("error")

is_ok(x)   // true
is_err(y)  // true

unwrap(x)  // 42
unwrap_or(y, 0)  // 0

map(x, fn(n) { n * 2 })  // Ok(84)
map_err(y, fn(e) { "Error: " <> e })  // Err("Error: error")
and_then(x, fn(n) { Ok(n * 2) })  // Ok(84)
```

---

## Ordering Type

### Definition

```tao
// Comparison result
type Ordering = LT | EQ | GT
```

### Operations

```tao
// Compare two values
fn compare(a: I32, b: I32) -> Ordering {
  if a < b {
    LT
  } else if a > b {
    GT
  } else {
    EQ
  }
}

// Reverse ordering
fn reverse(ord: Ordering) -> Ordering {
  match ord {
    | LT -> GT
    | EQ -> EQ
    | GT -> LT
  }
}

// Convert to string
fn to_string(ord: Ordering) -> String {
  match ord {
    | LT -> "LT"
    | EQ -> "EQ"
    | GT -> "GT"
  }
}
```

### Usage

```tao
compare(1, 2)  // LT
compare(2, 2)  // EQ
compare(3, 2)  // GT

reverse(LT)  // GT
to_string(EQ)  // "EQ"
```

---

## Function Combinators

### Identity

```tao
fn id<T>(x: T) -> T {
  x
}
```

### Composition

```tao
// Compose two functions: (f ∘ g)(x) = f(g(x))
fn compose<T, U, V>(f: fn(U) -> V, g: fn(T) -> U) -> fn(T) -> V {
  fn(x: T) -> V {
    f(g(x))
  }
}

// Pipe: x |> f |> g = g(f(x))
fn pipe<T, U>(x: T, f: fn(T) -> U) -> U {
  f(x)
}
```

### Application

```tao
// Apply function to argument
fn apply<T, U>(f: fn(T) -> U, x: T) -> U {
  f(x)
}

// Flip function arguments
fn flip<T, U, V>(f: fn(T) -> fn(U) -> V) -> fn(U) -> fn(T) -> V {
  fn(y: U) -> fn(T) -> V {
    fn(x: T) -> V {
      f(x)(y)
    }
  }
}
```

### Usage

```tao
let double = fn(x: I32) -> I32 { x * 2 }
let add_one = fn(x: I32) -> I32 { x + 1 }

let f = compose(double, add_one)  // fn(x) { (x + 1) * 2 }
f(5)  // 12

5 |> add_one |> double  // 12
```

---

## Implementation Plan

### Step 1: Register Prelude Constructors ✅

Prelude constructors need to be registered in the Core initial state:
- `True`, `False` (Bool)
- `Some`, `None` (Option)
- `Ok`, `Err` (Result)
- `LT`, `EQ`, `GT` (Ordering)

**Status**: 📋 **Pending** - Requires Core modification

### Step 2: Create Core Files 📋

Create `.core.tao` files in `lib/prelude/`:
- `bool.core.tao` - Boolean operations
- `option.core.tao` - Option operations
- `result.core.tao` - Result operations
- `ordering.core.tao` - Ordering operations

**Status**: ✅ **Complete** - Files created

### Step 3: Create Examples 📋

Create example files in `examples/stdlib/`:
- `prelude_bool.core.tao`
- `prelude_option.core.tao`
- `prelude_result.core.tao`
- `prelude_ordering.core.tao`

**Status**: ⏳ **In Progress** - Awaiting constructor registration

### Step 4: Create Tests 📋

Create test files in `test/stdlib/`:
- `prelude_test.gleam` - Gleam tests for prelude

**Status**: 📋 **Pending**

### Step 5: Auto-Import Prelude 📋

Update CLI to auto-import prelude for `.tao` files.

**Status**: 📋 **Pending**

---

## File Format

All prelude files use **Core language syntax** (`.core.tao` extension):

```tao
// lib/prelude/option.core.tao

// Type definition
type Option(a) = Some(a) | None

// Operations
fn is_some<T>(opt: Option(T)) -> Bool {
  match opt {
    | Some(_) -> True
    | None -> False
  }
}

// ... more operations
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Standard library overview
- **[03-numeric.md](./03-numeric.md)** - Numeric hierarchy
- **[../core/core.gleam](../../src/core/core.gleam)** - Core language implementation

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial specification created |
| March 2026 | Implementation started |
