# Tao Standard Library

> **Goal**: Minimal, composable standard library using Tao primitives
> **Status**: 📋 Designed
> **Date**: March 2025

---

## Status

### What's Working

- Core types designed (Maybe, Result, List)
- Combinators specified (map, and_then, fold, etc.)
- Operator overloading strategy defined
- Module structure planned

### What's Pending

- **Standard library implementation** (`src/tao/std/`)
- **Documentation and examples**
- **Performance benchmarks**
- **Additional modules** (Map, Set, String, etc.)

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[02-syntax.md](./02-syntax.md)** for Tao syntax
- See **[03-desugaring.md](./03-desugaring.md)** for desugaring rules

---

## Module Structure

```
src/tao/std/
├── maybe.gleam       # Maybe type (Some, None)
├── result.gleam      # Result type (Ok, Err)
├── list.gleam        # List type and operations
├── option.gleam      # Option combinators (alias for Maybe)
├── string.gleam      # String operations
├── char.gleam        # Character operations
├── num.gleam         # Numeric operations
├── bool.gleam        # Boolean operations
├── tuple.gleam       # Tuple types (Pair, Triple, etc.)
└── prelude.gleam     # Auto-imported basics
```

---

## Maybe Type

### Definition

```tao
type Maybe(a) {
  Some(a)
  None
}
```

### Constructors

```tao
fn some(x: a) -> Maybe(a) { Some(x) }
fn none() -> Maybe(a) { None }
```

### Combinators

```tao
// Map: Maybe(a) × (a → b) → Maybe(b)
fn map(m: Maybe(a), f: (a) -> b) -> Maybe(b) {
  match m {
    Some(x) => Some(f(x))
    None => None
  }
}

// And_then (flat_map): Maybe(a) × (a → Maybe(b)) → Maybe(b)
fn and_then(m: Maybe(a), f: (a) -> Maybe(b)) -> Maybe(b) {
  match m {
    Some(x) => f(x)
    None => None
  }
}

// Or_else: Maybe(a) × () → Maybe(a) → Maybe(a)
fn or_else(m: Maybe(a), default: () -> Maybe(a)) -> Maybe(a) {
  match m {
    Some(x) => Some(x)
    None => default()
  }
}

// Unwrap_or: Maybe(a) × a → a
fn unwrap_or(m: Maybe(a), default: a) -> a {
  match m {
    Some(x) => x
    None => default
  }
}

// Unwrap_or_else: Maybe(a) × () → a → a
fn unwrap_or_else(m: Maybe(a), default: () -> a) -> a {
  match m {
    Some(x) => x
    None => default()
  }
}

// Is_some: Maybe(a) → Bool
fn is_some(m: Maybe(a)) -> Bool {
  match m {
    Some(_) => true
    None => false
  }
}

// Is_none: Maybe(a) → Bool
fn is_none(m: Maybe(a)) -> Bool {
  match m {
    Some(_) => false
    None => true
  }
}

// Filter: Maybe(a) × (a → Bool) → Maybe(a)
fn filter(m: Maybe(a), pred: (a) -> Bool) -> Maybe(a) {
  match m {
    Some(x) if pred(x) => Some(x)
    _ => None
  }
}

// Zip: Maybe(a) × Maybe(b) → Maybe((a, b))
fn zip(m1: Maybe(a), m2: Maybe(b)) -> Maybe((a, b)) {
  match m1 {
    Some(x) => match m2 {
      Some(y) => Some((x, y))
      None => None
    }
    None => None
  }
}
```

### Usage Examples

```tao
// Using map
let x: Maybe(I32) = Some(5)
let y = map(x, fn(n) { n * 2 })  // Some(10)

// Using and_then (bind)
let z = and_then(x, fn(n) {
  if n > 0 { Some(n) } else { None }
})

// Using optional chaining syntax
let user = get_user()
let city = user?.address?.city  // Maybe(String)

// Using unwrap_or
let name = user?.name |> unwrap_or("Anonymous")
```

---

## Result Type

### Definition

```tao
type Result(a, e) {
  Ok(a)
  Err(e)
}
```

### Constructors

```tao
fn ok(x: a) -> Result(a, e) { Ok(x) }
fn err(e: e) -> Result(a, e) { Err(e) }
```

### Combinators

```tao
// Map: Result(a, e) × (a → b) → Result(b, e)
fn map(r: Result(a, e), f: (a) -> b) -> Result(b, e) {
  match r {
    Ok(x) => Ok(f(x))
    Err(e) => Err(e)
  }
}

// Map_err: Result(a, e) × (e → f) → Result(a, f)
fn map_err(r: Result(a, e), f: (e) -> f) -> Result(a, f) {
  match r {
    Ok(x) => Ok(x)
    Err(e) => Err(f(e))
  }
}

// And_then (flat_map): Result(a, e) × (a → Result(b, e)) → Result(b, e)
fn and_then(r: Result(a, e), f: (a) -> Result(b, e)) -> Result(b, e) {
  match r {
    Ok(x) => f(x)
    Err(e) => Err(e)
  }
}

// Or_else: Result(a, e) × (e → Result(a, f)) → Result(a, f)
fn or_else(r: Result(a, e), f: (e) -> Result(a, f)) -> Result(a, f) {
  match r {
    Ok(x) => Ok(x)
    Err(e) => f(e)
  }
}

// Unwrap_or: Result(a, e) × a → a
fn unwrap_or(r: Result(a, e), default: a) -> a {
  match r {
    Ok(x) => x
    Err(_) => default
  }
}

// Unwrap_or_else: Result(a, e) × (e → a) → a
fn unwrap_or_else(r: Result(a, e), default: (e) -> a) -> a {
  match r {
    Ok(x) => x
    Err(e) => default(e)
  }
}

// Unwrap: Result(a, e) → a (panics on Err)
fn unwrap(r: Result(a, e)) -> a {
  match r {
    Ok(x) => x
    Err(e) => panic("Unwrap called on Err: " <> inspect(e))
  }
}

// Expect: Result(a, e) × String → a (panics with message on Err)
fn expect(r: Result(a, e), msg: String) -> a {
  match r {
    Ok(x) => x
    Err(e) => panic(msg <> ": " <> inspect(e))
  }
}

// Is_ok: Result(a, e) → Bool
fn is_ok(r: Result(a, e)) -> Bool {
  match r {
    Ok(_) => true
    Err(_) => false
  }
}

// Is_err: Result(a, e) → Bool
fn is_err(r: Result(a, e)) -> Bool {
  match r {
    Ok(_) => false
    Err(_) => true
  }
}

// To_option: Result(a, e) → Maybe(a) (discards error)
fn to_option(r: Result(a, e)) -> Maybe(a) {
  match r {
    Ok(x) => Some(x)
    Err(_) => None
  }
}
```

### Usage Examples

```tao
// Using bind operator
fn process() -> Result(I32, String) {
  let x <- parse_int("42")
  let y <- parse_int("10")
  Ok(x + y)
}

// Using map
let r: Result(I32, String) = Ok(5)
let doubled = map(r, fn(n) { n * 2 })  // Ok(10)

// Using map_err
let with_msg = map_err(r, fn(e) { "Error: " <> e })

// Using optional chaining syntax
let value = read_file("config.txt")?  // Result(String, Error)
```

---

## List Type

### Definition

```tao
type List(a) {
  Nil
  Cons(a, List(a))
}

// Syntax sugar
[1, 2, 3]  // Cons(1, Cons(2, Cons(3, Nil)))
[]         // Nil
```

### Constructors

```tao
fn empty() -> List(a) { Nil }
fn singleton(x: a) -> List(a) { Cons(x, Nil) }
fn cons(x: a, xs: List(a)) -> List(a) { Cons(x, xs) }
fn list(x1, x2, ..xs) -> List(a) { ... }  // Variadic
```

### Basic Operations

```tao
// Length: List(a) → I32
fn length(xs: List(a)) -> I32 {
  match xs {
    Nil => 0
    Cons(_, rest) => 1 + length(rest)
  }
}

// Head: List(a) → Maybe(a)
fn head(xs: List(a)) -> Maybe(a) {
  match xs {
    Nil => None
    Cons(x, _) => Some(x)
  }
}

// Tail: List(a) → Maybe(List(a))
fn tail(xs: List(a)) -> Maybe(List(a)) {
  match xs {
    Nil => None
    Cons(_, rest) => Some(rest)
  }
}

// Append: List(a) × List(a) → List(a)
fn append(xs: List(a), ys: List(a)) -> List(a) {
  match xs {
    Nil => ys
    Cons(x, rest) => Cons(x, append(rest, ys))
  }
}

// Reverse: List(a) → List(a)
fn reverse(xs: List(a)) -> List(a) {
  fn go(acc: List(a), remaining: List(a)) -> List(a) {
    match remaining {
      Nil => acc
      Cons(x, rest) => go(Cons(x, acc), rest)
    }
  }
  go(Nil, xs)
}
```

### Higher-Order Operations

```tao
// Map: List(a) × (a → b) → List(b)
fn map(xs: List(a), f: (a) -> b) -> List(b) {
  match xs {
    Nil => Nil
    Cons(x, rest) => Cons(f(x), map(rest, f))
  }
}

// Filter: List(a) × (a → Bool) → List(a)
fn filter(xs: List(a), pred: (a) -> Bool) -> List(a) {
  match xs {
    Nil => Nil
    Cons(x, rest) => {
      if pred(x) {
        Cons(x, filter(rest, pred))
      } else {
        filter(rest, pred)
      }
    }
  }
}

// Fold (fold_left): List(a) × b × (b → a → b) → b
fn fold(xs: List(a), init: b, f: (b, a) -> b) -> b {
  match xs {
    Nil => init
    Cons(x, rest) => fold(rest, f(init, x), f)
  }
}

// Fold_right: List(a) × b × (a → b → b) → b
fn fold_right(xs: List(a), init: b, f: (a, b) -> b) -> b {
  match xs {
    Nil => init
    Cons(x, rest) => f(x, fold_right(rest, init, f))
  }
}

// Flat_map: List(a) × (a → List(b)) → List(b)
fn flat_map(xs: List(a), f: (a) -> List(b)) -> List(b) {
  fold(xs, Nil, fn(acc, x) { append(acc, f(x)) })
}

// For_each: List(a) × (a → Unit) → Unit
fn for_each(xs: List(a), f: (a) -> Unit) -> Unit {
  match xs {
    Nil => ()
    Cons(x, rest) => { f(x); for_each(rest, f) }
  }
}
```

### Predicates

```tao
// All: List(a) × (a → Bool) → Bool
fn all(xs: List(a), pred: (a) -> Bool) -> Bool {
  match xs {
    Nil => true
    Cons(x, rest) => pred(x) && all(rest, pred)
  }
}

// Any: List(a) × (a → Bool) → Bool
fn any(xs: List(a), pred: (a) -> Bool) -> Bool {
  match xs {
    Nil => false
    Cons(x, rest) => pred(x) || any(rest, pred)
  }
}

// Contains: List(a) × a → Bool (requires Eq)
fn contains(xs: List(a), target: a) -> Bool {
  any(xs, fn(x) { x == target })
}

// Find: List(a) × (a → Bool) → Maybe(a)
fn find(xs: List(a), pred: (a) -> Bool) -> Maybe(a) {
  match xs {
    Nil => None
    Cons(x, rest) => {
      if pred(x) { Some(x) } else { find(rest, pred) }
    }
  }
}
```

### Transformation

```tao
// Take: List(a) × I32 → List(a)
fn take(xs: List(a), n: I32) -> List(a) {
  if n <= 0 {
    Nil
  } else {
    match xs {
      Nil => Nil
      Cons(x, rest) => Cons(x, take(rest, n - 1))
    }
  }
}

// Drop: List(a) × I32 → List(a)
fn drop(xs: List(a), n: I32) -> List(a) {
  if n <= 0 {
    xs
  } else {
    match xs {
      Nil => Nil
      Cons(_, rest) => drop(rest, n - 1)
    }
  }
}

// Take_while: List(a) × (a → Bool) → List(a)
fn take_while(xs: List(a), pred: (a) -> Bool) -> List(a) {
  match xs {
    Nil => Nil
    Cons(x, rest) => {
      if pred(x) {
        Cons(x, take_while(rest, pred))
      } else {
        Nil
      }
    }
  }
}

// Drop_while: List(a) × (a → Bool) → List(a)
fn drop_while(xs: List(a), pred: (a) -> Bool) -> List(a) {
  match xs {
    Nil => Nil
    Cons(x, rest) => {
      if pred(x) {
        drop_while(rest, pred)
      } else {
        xs
      }
    }
  }
}

// Zip: List(a) × List(b) → List((a, b))
fn zip(xs: List(a), ys: List(b)) -> List((a, b)) {
  match xs {
    Nil => Nil
    Cons(x, rest_x) => {
      match ys {
        Nil => Nil
        Cons(y, rest_y) => Cons((x, y), zip(rest_x, rest_y))
      }
    }
  }
}

// Enumerate: List(a) → List((I32, a))
fn enumerate(xs: List(a)) -> List((I32, a)) {
  fn go(i: I32, acc: List((I32, a)), remaining: List(a)) -> List((I32, a)) {
    match remaining {
      Nil => reverse(acc)
      Cons(x, rest) => go(i + 1, Cons((i, x), acc), rest)
    }
  }
  go(0, Nil, xs)
}
```

### Usage Examples

```tao
// Using pipe operator
let result = nums
  |> filter(fn(x) { x % 2 == 0 })
  |> map(fn(x) { x * 2 })
  |> fold(0, fn(acc, x) { acc + x })

// Using for comprehension (syntax sugar for flat_map)
let pairs = for x in [1, 2, 3], y in [4, 5, 6] {
  (x, y)
}
// Desugars to:
// flat_map([1, 2, 3], fn(x) {
//   flat_map([4, 5, 6], fn(y) {
//     singleton((x, y))
//   })
// })
```

---

## Numeric Operations

### Integer Operations

```tao
// Arithmetic (overloaded operators)
fn add(a: I32, b: I32) -> I32 { a + b }
fn sub(a: I32, b: I32) -> I32 { a - b }
fn mul(a: I32, b: I32) -> I32 { a * b }
fn div(a: I32, b: I32) -> Result(I32, DivError) {
  if b == 0 { Err(DivByZero) } else { Ok(a / b) }
}
fn mod(a: I32, b: I32) -> Result(I32, DivError) {
  if b == 0 { Err(DivByZero) } else { Ok(a % b) }
}

// Comparison
fn eq(a: I32, b: I32) -> Bool { a == b }
fn neq(a: I32, b: I32) -> Bool { a != b }
fn lt(a: I32, b: I32) -> Bool { a < b }
fn lte(a: I32, b: I32) -> Bool { a <= b }
fn gt(a: I32, b: I32) -> Bool { a > b }
fn gte(a: I32, b: I32) -> Bool { a >= b }

// Min/Max
fn min(a: I32, b: I32) -> I32 { if a < b { a } else { b } }
fn max(a: I32, b: I32) -> I32 { if a > b { a } else { b } }

// Abs
fn abs(a: I32) -> I32 { if a < 0 { -a } else { a } }
```

### Float Operations

```tao
// Same as integers, but for F64
fn add(a: F64, b: F64) -> F64 { a + b }
fn sub(a: F64, b: F64) -> F64 { a - b }
fn mul(a: F64, b: F64) -> F64 { a * b }
fn div(a: F64, b: F64) -> F64 { a / b }

// Math functions
fn sqrt(a: F64) -> F64 { ... }
fn sin(a: F64) -> F64 { ... }
fn cos(a: F64) -> F64 { ... }
fn exp(a: F64) -> F64 { ... }
fn log(a: F64) -> F64 { ... }
fn pow(base: F64, exp: F64) -> F64 { ... }
```

### Operator Overloading

```tao
// All numeric types use same operators
fn add(a: I32, b: I32) -> I32 { i32_add(a, b) }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }
fn add(a: Vec3, b: Vec3) -> Vec3 { vec3_add(a, b) }

// Usage (type inference resolves overload)
let x = 1 + 2           // I32
let y = 1.0 + 2.0       // F64
let z = vec3(1, 2, 3) + vec3(4, 5, 6)  // Vec3
```

---

## String Operations

### Basic Operations

```tao
// Length: String → I32
fn length(s: String) -> I32 { ... }

// Concat: String × String → String
fn concat(a: String, b: String) -> String { a <> b }

// Contains: String × String → Bool
fn contains(haystack: String, needle: String) -> Bool { ... }

// Starts_with: String × String → Bool
fn starts_with(s: String, prefix: String) -> Bool { ... }

// Ends_with: String × String → Bool
fn ends_with(s: String, suffix: String) -> Bool { ... }
```

### Transformation

```tao
// To_uppercase: String → String
fn to_uppercase(s: String) -> String { ... }

// To_lowercase: String → String
fn to_lowercase(s: String) -> String { ... }

// Trim: String → String
fn trim(s: String) -> String { ... }

// Replace: String × String × String → String
fn replace(s: String, from: String, to: String) -> String { ... }

// Split: String × String → List(String)
fn split(s: String, sep: String) -> List(String) { ... }

// Join: List(String) × String → String
fn join(xs: List(String), sep: String) -> String { ... }
```

### Conversion

```tao
// To_int: String → Result(I32, ParseError)
fn to_int(s: String) -> Result(I32, ParseError) { ... }

// To_float: String → Result(F64, ParseError)
fn to_float(s: String) -> Result(F64, ParseError) { ... }

// From_int: I32 → String
fn from_int(n: I32) -> String { ... }

// From_float: F64 → String
fn from_float(n: F64) -> String { ... }
```

---

## Tuple Types

### Definition

```tao
type Pair(a, b) = (a, b)
type Triple(a, b, c) = (a, b, c)
// ... up to Tuple8
```

### Operations

```tao
// First: (a, b) → a
fn first(t: (a, b)) -> a {
  match t {
    (x, _) => x
  }
}

// Second: (a, b) → b
fn second(t: (a, b)) -> b {
  match t {
    (_, y) => y
  }
}

// Swap: (a, b) → (b, a)
fn swap(t: (a, b)) -> (b, a) {
  match t {
    (x, y) => (y, x)
  }
}

// Map_first: (a, b) × (a → c) → (c, b)
fn map_first(t: (a, b), f: (a) -> c) -> (c, b) {
  match t {
    (x, y) => (f(x), y)
  }
}

// Map_second: (a, b) × (b → c) → (a, c)
fn map_second(t: (a, b), f: (b) -> c) -> (a, c) {
  match t {
    (x, y) => (x, f(y))
  }
}
```

---

## Prelude

The prelude is auto-imported in every Tao module:

```tao
// Types
Maybe, Some, None
Result, Ok, Err
List, Nil, Cons
Option  // Alias for Maybe

// Functions
map, and_then, or_else  // Maybe/Result
length, head, tail, map, filter, fold  // List
inspect  // Debug printing

// Operators
+, -, *, /, %, ==, !=, <, >, <=, >=, &&, ||, !
<-, ?.  // Bind and optional chaining
```

---

## Implementation Plan

### Phase 1: Core Types

- [ ] Maybe type and combinators
- [ ] Result type and combinators
- [ ] List type and basic operations

### Phase 2: Higher-Order Functions

- [ ] List map, filter, fold
- [ ] List flat_map, for_each
- [ ] List predicates (all, any, find)

### Phase 3: Additional Types

- [ ] String operations
- [ ] Numeric operations
- [ ] Tuple types

### Phase 4: Polish

- [ ] Documentation
- [ ] Examples
- [ ] Performance optimization
- [ ] Additional modules (Map, Set, etc.)

---

## References

- [Tao Overview](./01-overview.md)
- [Tao Syntax](./02-syntax.md)
- [Haskell Prelude](https://hackage.haskell.org/package/base/docs/Prelude.html)
- [Rust std::option](https://doc.rust-lang.org/std/option/)
- [Rust std::result](https://doc.rust-lang.org/std/result/)
- [OCaml List module](https://ocaml.org/api/List.html)
