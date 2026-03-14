# Standard Library Overview

> **Goal**: Provide a minimal, pragmatic standard library for Tao with essential types and operations
> **Status**: ⏳ **In Progress** - Phase 1 (Prelude) constructors registered with type parameters
> **Date**: March 2026

---

## Status

### What's Working

- ✅ Core language with implicit arguments and type matching
- ✅ Tao parser and desugarer with full operator support
- ✅ CLI integration for running Tao files
- ✅ **424 tests passing**
- ✅ Prelude library files created (`lib/prelude/*.core.tao`)
- ✅ Prelude constructors auto-imported with type parameters (`True`, `False`, `Some`, `None`, `Ok`, `Err`, `LT`, `EQ`, `GT`)
- ✅ Type parameter instantiation for constructors

### What's Pending

- 📋 **Match Type Checking** - Fix match expression type checking for constructor values
- 📋 **Proper Return Types** - Define actual return types (e.g., `Bool`, `Option(a)`) instead of `I32T` placeholder
- 📋 **Working Examples** - Examples awaiting full type system support
- 📋 **Phase 2: Numeric Hierarchy** - Type classes for numeric operations
- 📋 **Phase 3: Collections** - List, Vector, Map
- 📋 **Phase 4: String and I/O** - String operations, file I/O
- 📋 **Phase 5: Advanced** - Monad utilities, function combinators

### Related

- See **[02-prelude.md](./02-prelude.md)** for Prelude specification
- See **[03-numeric.md](./03-numeric.md)** for Numeric Hierarchy
- See **[04-collections.md](./04-collections.md)** for Collections
- See **[../tao/10-overloading.md](../tao/10-overloading.md)** for overloading mechanism

---

## Core Principle

**Minimal and Pragmatic**: The standard library provides only essential types and operations. Everything is built on Tao's core features (implicit arguments, type matching) without adding complexity.

### Design Goals

1. **Type-safe** - Leverage dependent types for correctness
2. **Zero overhead** - Type resolution at compile time
3. **Composable** - Small, focused modules that work together
4. **Documented** - Every function has clear semantics

---

## Architecture

### Module Structure

```
lib/
├── prelude/           # Core types (auto-imported)
│   ├── prelude.tao    # Main prelude module
│   ├── bool.tao       # Boolean type and operations
│   ├── option.tao     # Option type
│   └── result.tao     # Result type
├── math/              # Numeric operations
│   ├── int.tao        # Integer operations
│   ├── float.tao      # Floating-point operations
│   └── num.tao        # Numeric type class
├── collections/       # Data structures
│   ├── list.tao       # Linked list
│   ├── vector.tao     # Dynamic array
│   └── map.tao        # Hash map
├── string/            # String operations
│   └── string.tao     # String type and functions
└── io/                # I/O operations
    └── io.tao         # File and console I/O
```

### Import System

```tao
// Prelude is auto-imported (no import needed)
let x: Option(I32) = Some(42)

// Explicit imports for other modules
import math/int
import collections/list
import string/string
```

---

## Library Overview

### Prelude (Auto-imported)

**Purpose**: Essential types used in almost every program.

| Type | Description | Example |
|------|-------------|---------|
| `Bool` | Boolean type (`true`/`false`) | `true && false` |
| `Option(a)` | Optional value (`Some(x)` or `None`) | `Some(42)`, `None` |
| `Result(a, e)` | Result with error (`Ok(x)` or `Err(e)`) | `Ok(42)`, `Err("error")` |
| `Ordering` | Comparison result (`LT`, `EQ`, `GT`) | `compare(1, 2) = LT` |

**Functions**:
- `not: Bool -> Bool`
- `and: Bool -> Bool -> Bool`
- `or: Bool -> Bool -> Bool`
- `is_some: Option(a) -> Bool`
- `is_none: Option(a) -> Bool`
- `unwrap: Option(a) -> a` (panics on None)
- `is_ok: Result(a, e) -> Bool`
- `is_err: Result(a, e) -> Bool`

---

### Math Library

**Purpose**: Numeric operations and type classes.

| Module | Description |
|--------|-------------|
| `math/int` | Integer operations (abs, min, max, etc.) |
| `math/float` | Floating-point operations |
| `math/num` | Numeric type class (Add, Sub, Mul, Div) |

**Example**:
```tao
import math/int

let x = int.abs(-42)      // 42
let y = int.min(10, 20)   // 10
let z = int.max(10, 20)   // 20
```

---

### Collections Library

**Purpose**: Common data structures.

| Module | Description |
|--------|-------------|
| `collections/list` | Immutable linked list |
| `collections/vector` | Dynamic array with random access |
| `collections/map` | Hash map (key-value store) |

**Example**:
```tao
import collections/list

let xs = list.cons(1, list.cons(2, list.nil))
let ys = list.map(fn(x) { x * 2 }, xs)  // [2, 4]
```

---

### String Library

**Purpose**: String manipulation.

| Function | Description |
|----------|-------------|
| `length: String -> Int` | Get string length |
| `concat: String -> String -> String` | Concatenate strings |
| `slice: String -> Int -> Int -> String` | Extract substring |

---

### I/O Library

**Purpose**: Input/output operations.

| Function | Description |
|----------|-------------|
| `print: String -> Unit` | Print to console |
| `read_file: String -> Result(String, Error)` | Read file contents |
| `write_file: String -> String -> Result(Unit, Error)` | Write file |

---

## Design Principles

### 1. **Type Classes via Overloading**

Numeric operations use Tao's overloading mechanism:

```tao
// Type class for addition
fn (+)(a: I32, b: I32) -> I32 { a + b }
fn (+)(a: F64, b: F64) -> F64 { a + b }

// Generic function using overloaded operator
fn add<T>(a: T, b: T) -> T { a + b }
```

### 2. **Option/Result for Error Handling**

No exceptions - use `Option` for missing values, `Result` for errors:

```tao
// Safe division
fn div(a: I32, b: I32) -> Result(I32, String) {
  if b == 0 {
    Err("division by zero")
  } else {
    Ok(a / b)
  }
}
```

### 3. **Immutability by Default**

All collections are immutable. Mutable operations return new values:

```tao
let xs = [1, 2, 3]
let ys = list.cons(0, xs)  // [0, 1, 2, 3], xs unchanged
```

---

## Example Usage

### Basic Prelude

```tao
// Option type
let x: Option(I32) = Some(42)
let y: Option(I32) = None

match x {
  | Some(n) -> print("Got: " <> int.to_string(n))
  | None -> print("Got nothing")
}

// Result type
let result: Result(I32, String) = div(10, 2)

match result {
  | Ok(n) -> print("Result: " <> int.to_string(n))
  | Err(e) -> print("Error: " <> e)
}
```

### Numeric Operations

```tao
import math/int

// Generic numeric function
fn double<T: Num>(x: T) -> T {
  x * T(2)
}

let a = double(21)      // 42 (I32)
let b = double(21.0)    // 42.0 (F64)
```

### Collections

```tao
import collections/list
import collections/vector

// List operations
let xs = [1, 2, 3]
let ys = list.map(fn(x) { x * 2 }, xs)
let sum = list.fold(fn(acc, x) { acc + x }, 0, xs)

// Vector operations
let v = vector.from_list(xs)
let elem = vector.get(v, 1)  // Some(2)
```

---

## Implementation Phases

### Phase 1: Prelude (Current)

**Goal**: Essential types for basic programming.

- [ ] `Bool` type and operations
- [ ] `Option(a)` type and operations
- [ ] `Result(a, e)` type and operations
- [ ] `Ordering` type
- [ ] Basic function combinators

**Estimated**: 1-2 weeks

---

### Phase 2: Numeric Hierarchy

**Goal**: Type-safe numeric operations.

- [ ] `Num` type class (Add, Sub, Mul)
- [ ] `Fractional` type class (Div)
- [ ] `Comparable` type class (compare, min, max)
- [ ] `math/int` module
- [ ] `math/float` module

**Estimated**: 1-2 weeks

---

### Phase 3: Collections

**Goal**: Common data structures.

- [ ] `List(a)` - Immutable linked list
- [ ] `Vector(a)` - Dynamic array
- [ ] `Map(k, v)` - Hash map
- [ ] Standard operations (map, filter, fold)

**Estimated**: 2-3 weeks

---

### Phase 4: String and I/O

**Goal**: Text and file operations.

- [ ] `String` type and operations
- [ ] Console I/O (print, read_line)
- [ ] File I/O (read_file, write_file)

**Estimated**: 1-2 weeks

---

### Phase 5: Advanced

**Goal**: Utility functions and combinators.

- [ ] Function combinators (compose, pipe)
- [ ] Monad utilities (bind, sequence)
- [ ] Testing utilities

**Estimated**: 1-2 weeks

---

## Testing Strategy

### Example-Based Tests

Each module has example files in `examples/stdlib/`:

```
examples/stdlib/
├── prelude_option.tao
├── prelude_result.tao
├── math_int.tao
└── collections_list.tao
```

### Test Commands

```bash
# Type-check a stdlib example
gleam run check examples/stdlib/prelude_option.tao

# Run a stdlib example
gleam run run examples/stdlib/prelude_option.tao
```

### Golden Files

Expected outputs stored in `examples/stdlib/*.output.txt`:

```bash
# Compare output with golden file
diff <(gleam run run examples/stdlib/foo.tao) examples/stdlib/foo.output.txt
```

---

## Related Documents

- **[02-prelude.md](./02-prelude.md)** - Prelude specification
- **[03-numeric.md](./03-numeric.md)** - Numeric hierarchy
- **[04-collections.md](./04-collections.md)** - Collections specification
- **[../tao/10-overloading.md](../tao/10-overloading.md)** - Overloading mechanism
- **[../core/16-implicit-arguments-status.md](../core/16-implicit-arguments-status.md)** - Implicit arguments

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial plan created |
| March 2026 | Phase 1 (Prelude) started |
