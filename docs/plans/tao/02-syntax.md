# Tao Syntax Specification

> **Goal**: TypeScript-like syntax with functional semantics
> **Status**: 📋 Designed
> **Date**: March 2025

---

## Status

### What's Working

- Syntax design complete
- Operator precedence defined
- Type system specified
- Pattern matching syntax defined
- Error handling sugar specified (`<-`, `?.`, `?`)

### What's Pending

- **Lexer implementation** (`src/tao/lexer.gleam`)
- **Grammar definition** (`src/tao/grammar.gleam`)
- **Parser implementation** (`src/tao/parser.gleam`)
- **Formatter implementation** (`src/tao/formatter.gleam`)

### Related

- See **[01-overview.md](./01-overview.md)** for overall implementation status
- See **[03-desugaring.md](./03-desugaring.md)** for desugaring rules
- See **[../../syntax-library.md](../../syntax-library.md)** for syntax library usage

---

## Lexical Structure

### Keywords

```
let, mut, fn, type, match, if, else, return
import, as, comptime, do
```

Note: `true`, `false`, `Some`, `None`, `Ok`, `Err`, etc. are **not keywords**—they're regular constructors from the standard library.

### Literals

```tao
42              // Integer literal (inferred as I32 by default)
3.14            // Float literal (inferred as F64 by default)
"hello"         // String literal
"hello\nworld"  // With escape sequences
```

**Important**: Literals are **untyped**. They're just values. Type inference determines the actual type:
- `let x = 42` infers to `I32` (default)
- `let x: F32 = 42` infers to `F32` (annotation)
- `let x: U32 = 42` is valid (fits in range)
- `let x: U32 = -1` is **invalid** (negative doesn't fit in U32)

Type checking validates that literal values fit in the inferred/constrained type.

### Identifiers

```tao
lowercase       // Variables, functions
snake_case      // Preferred for functions
Uppercase       // Types, constructors
PascalCase      // Preferred for types
_name           // Private (module-internal)
```

### Operators

```
// Arithmetic
+  -  *  /  %

// Comparison
==  !=  <  >  <=  >=

// Logical
&&  ||  !

// Other
.   ?.   ?   <-   |>   =   :   ->   <|
```

### Comments

```tao
// Line comment

/* Block comment */

/*
 * Multi-line
 * block comment
 */
```

---

## Type System

### Type Variables

Type variables are **explicitly marked** with angle brackets to distinguish them from value variables:

```tao
// Generic function with explicit type parameter
fn identity<a>(x: a) -> a {
  x
}

// Multiple type parameters
fn map<a, b>(list: List(a), f: fn(a) -> b) -> List(b) {
  // Implementation
}

// Type parameters can have constraints (future feature)
fn add<n: Num>(a: n, b: n) -> n {
  a + b
}
```

**Why explicit type parameters?**
- Distinguishes `a` (type variable) from `a` (value variable)
- Clear at call site: `identity<Int>(5)`
- Avoids confusion with undefined value variables

### Standard Library Types

The following are **not primitives**—they're defined in the standard library:

```tao
// Boolean type
type Bool = True | False

// String type (list of characters)
type String = List(Char)

// Unit type (empty tuple)
type Unit = ()

// Common types
type Maybe(a) = Some(a) | None
type Result(a, e) = Ok(a) | Err(e)
type List(a) = Cons(a, List(a)) | Nil
```

### Type Definitions

#### Type Aliases

```tao
// Simple alias
type String = List(Char)

// Alias with type parameters
type Result(a, e) = Either(e, a)

// Alias to record
type Point = { x: Int, y: Int }
```

#### Record Types

Record types always use `= { ... }`:

```tao
type Point = {
  x: Int,
  y: Int,
}

type Person = {
  name: String,
  age: Int,
  address: Maybe(Address),
}
```

#### Sum Types (Algebraic Data Types)

Sum types use `= | ... | ...` or just `= Constructor`:

```tao
// Single-line
type Bool = True | False
type Maybe(a) = Some(a) | None

// Multi-line with pipes
type Result(a, e) =
  | Ok(a)
  | Err(e)

type Expr =
  | Num(Int)
  | Add(Expr, Expr)
  | Mul(Expr, Expr)

// Mixed style
type List(a) = Nil | Cons(a, List(a))
```

**Syntax rules**:
- Always starts with `type Name = `
- Constructors start with uppercase
- Multiple constructors separated by `|`
- Can be single-line or multi-line
- Multi-line can start with `|` (optional first pipe)

#### GADTs (Generalized Algebraic Data Types)

```tao
// Type indexed by value
type Vec(n: Int, a: Type) =
  | Nil: Vec(0, a)
  | Cons: (a, Vec(n, a)) -> Vec(n + 1, a)

// Type-indexed expressions
type Expr(t: Type) =
  | Num: Int -> Expr(F64)
  | Add: (Expr(F64), Expr(F64)) -> Expr(F64)
  | If: (Expr(Bool), Expr(t), Expr(t)) -> Expr(t)
```

---

## Variables and Bindings

### Immutable (Default)

```tao
let x = 42
let y: F64 = 3.14
let text = "hello"
```

### Mutable (Explicit)

```tao
let mut counter = 0
counter = counter + 1
counter = counter * 2
```

### Shadowing

```tao
let x = 5
let x = "hello"  // OK, new binding shadows old
```

### Pattern Binding

```tao
let { x, y } = point       // Destructure record
let Some(value) = maybe    // Destructure Maybe
let [head, ..tail] = list  // Destructure list
```

### Imperative Blocks

```tao
// Mutable variables in a do block
let result = do {
  mut sum = 0
  mut i = 0
  while i < 10 {
    sum = sum + i
    i = i + 1
  }
  sum  // Final expression is block value
}

// With early return
let found = do {
  for x in list {
    if x == target { return Some(x) }
  }
  None
}

// For loop (desugars to fold/map)
let doubled = do {
  for x in [1, 2, 3] {
    x * 2
  }
}
// Desugars to: list.map([1, 2, 3], fn(x) { x * 2 })
```

**Note**: Use `do { ... }` for imperative blocks with statements separated by `;` or newlines.

---

## Functions

### Basic Function

```tao
fn add(a: Int, b: Int) -> Int {
  a + b
}
```

### Generic Function

```tao
// Explicit type parameters
fn identity<a>(x: a) -> a {
  x
}

fn map<a, b>(list: List(a), f: fn(a) -> b) -> List(b) {
  // Implementation
}
```

### Overloaded Function

```tao
// Same name, different type signatures
fn add(a: Int, b: Int) -> Int { int_add(a, b) }
fn add(a: F64, b: F64) -> F64 { float_add(a, b) }
fn add(a: String, b: String) -> String { string_concat(a, b) }

// Usage (type inference resolves overload)
let x = 1 + 2           // Int
let y = 1.0 + 2.0       // F64
let z = "a" + "b"       // "ab"
```

### Anonymous Function

```tao
let double = fn(x: Int) -> Int { x * 2 }
let add = fn(a, b) { a + b }
```

### Lambda with Type Parameters

```tao
// Lambda with explicit type parameter
let id = fn<a>(x: a) -> a { x }
```

---

## Types and Data

### Record Type

```tao
type Point = {
  x: Int,
  y: Int,
}

type Person = {
  name: String,
  age: Int,
  address: Maybe(Address),
}
```

### Record Value

```tao
let p = { x: 1.0, y: 2.0 }
let person = {
  name: "Alice",
  age: 30,
  address: None,
}
```

### Field Access

```tao
p.x
person.name
person.address?.city  // Optional chaining
```

### Record Update

```tao
let p2 = { ..p, y: 3.0 }  // Copy p, change y
let person2 = { ..person, age: 31 }  // Copy with update
```

### Sum Type (Algebraic Data Type)

```tao
type Maybe(a) = Some(a) | None

type Result(a, e) = Ok(a) | Err(e)

type List(a) = Nil | Cons(a, List(a))

type Bool = True | False
```

### Constructor Usage

```tao
// Constructors are just functions
let some_val = Some(42)
let none_val = None
let ok_val = Ok(100)
let err_val = Err("error")
let true_val = True
let false_val = False

// Note: true/false are NOT literals, they're constructors
```

### GADT

```tao
type Vec(n: Int, a: Type) =
  | Nil: Vec(0, a)
  | Cons: (a, Vec(n, a)) -> Vec(n + 1, a)

type Expr(t: Type) =
  | Num: Int -> Expr(F64)
  | Add: (Expr(F64), Expr(F64)) -> Expr(F64)
  | If: (Expr(Bool), Expr(t), Expr(t)) -> Expr(t)
```

---

## Pattern Matching

### Basic Match (OCaml Style)

```tao
match value {
  | Some(x) -> x
  | None -> 0
}
```

**Note**: Uses `|` as delimiter and `->` for branches (same as lambda).

### With Guards

```tao
fn classify(n: Int) -> String {
  match n {
    | x if x < 0 -> "negative"
    | x if x == 0 -> "zero"
    | x if x > 0 -> "positive"
  }
}
```

### Nested Patterns

```tao
match list {
  | Cons(head, Cons(second, Nil)) -> Some(second)
  | _ -> None
}
```

### Record Patterns

```tao
match person {
  | { name: "Alice", age: _ } -> "Found Alice"
  | { name: n, age: a } -> n <> " is " <> a
}
```

### Or Patterns

```tao
match value {
  | Some(0) | None -> "zero or nothing"
  | Some(x) -> "something: " <> x
}
```

### Multiple Patterns with Same Body

```tao
match x {
  | 0 | 1 | 2 -> "small"
  | 3 | 4 | 5 -> "medium"
  | _ -> "large"
}
```

---

## Error Handling

### Result Type

```tao
type Result(a, e) = Ok(a) | Err(e)
```

### Bind Operator (`<-`)

```tao
fn process() -> Result(Int, String) {
  let x <- parse_int("42")  // Unwraps Ok, returns early on Err
  let y <- parse_int("10")
  Ok(x + y)
}
```

### Optional Chaining (`?`)

```tao
// For Result
fn read_config() -> Result(Config, Error) {
  let data = read_file("config.txt")?  // Unwraps Ok, returns on Err
  let config = parse_config(data)?
  Ok(config)
}

// For Maybe
let city = user?.address?.city  // Maybe(String)
```

### Pattern Matching on Result

```tao
match result {
  | Ok(x) -> print(x)
  | Err(e) -> print("Error: " <> e)
}
```

---

## Control Flow

### If/Else

```tao
if x > 0 {
  "positive"
} else if x < 0 {
  "negative"
} else {
  "zero"
}

// If without else returns Unit
if condition {
  do_something()
}
```

### Match as Expression

```tao
let result = match value {
  | Some(x) -> x
  | None -> default
}
```

### Early Return

```tao
fn find_positive(nums: List(Int)) -> Maybe(Int) {
  match nums {
    | Nil -> return None
    | Cons(x, _) if x > 0 -> return Some(x)
    | Cons(_, xs) -> find_positive(xs)
  }
}
```

### Do Blocks

```tao
// Imperative computation
let result = do {
  mut acc = 0
  for i in range(0, 10) {
    acc = acc + i
  }
  acc
}

// With statements separated by semicolons
let _ = do {
  print("hello");
  print("world");
  42
}
```

---

## Operators

### Operator Precedence (highest to lowest)

| Prec | Operator | Assoc | Description |
|------|----------|-------|-------------|
| 100 | `.`, `?.` | Left | Field access, optional chaining |
| 90 | `!` | Right | Logical not |
| 80 | `*`, `/`, `%` | Left | Multiplication, division, modulo |
| 70 | `+`, `-` | Left | Addition, subtraction |
| 60 | `<`, `>`, `<=`, `>=` | Left | Comparison |
| 50 | `==`, `!=` | Left | Equality |
| 40 | `&&` | Left | Logical and |
| 30 | `||` | Left | Logical or |
| 20 | `<-` | Right | Bind operator |
| 10 | `\|>` | Left | Pipe operator |

### Operator Examples

```tao
// Field access binds tightest
user.address.city

// Then arithmetic
1 + 2 * 3  // = 1 + (2 * 3)

// Then comparison
x < y && y < z  // = (x < y) && (y < z)

// Then logical
a || b && c  // = a || (b && c)

// Bind operator
let x <- f()  // Binds result of f()

// Pipe operator (lowest precedence)
x |> f |> g  // = g(f(x))
```

---

## Attributes

### Permission Attribute

```tao
@permission(Read("/tmp"))
fn read_temp() -> Result(String, Error) {
  read_file("/tmp/data.txt")
}

@permission(Write("/tmp"))
fn write_temp(content: String) -> Result(Unit, Error) {
  write_file("/tmp/data.txt", content)
}

@permission(Read("*"))  // Wildcard
fn read_any(path: String) -> Result(String, Error) {
  read_file(path)
}
```

### Effect Attribute

```tao
@effect(IO)
fn print(msg: String) -> Unit {
  // Has side effects
}

@effect(Random)
fn random() -> Int {
  // Uses random number generator
}
```

### Inline Attribute

```tao
@inline
fn fast_double(x: Int) -> Int {
  x * 2
}
```

### Comptime

```tao
// Comptime expression
let x = comptime factorial(5)

// Comptime with do block
let config = comptime do {
  let size = 1024
  load_config(size)
}

// Comptime function
@comptime
fn factorial(n: Int) -> Int {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let fact_5 = factorial(5)  // Evaluated at compile-time: 120
```

**Note**: `comptime` takes an expression. For blocks, use `comptime do { ... }`.

---

## Modules

### Module Declaration

```tao
module my_app/utils
```

### Visibility

- **Public by default**: All names are exported unless they start with `_`
- **Private names**: Start with `_` (underscore)

```tao
// Public function
fn helper() -> Unit { ... }

// Private function (module-internal only)
fn _internal_helper() -> Unit { ... }

// Public type
type Point = { x: Int, y: Int }

// Private type
type _InternalState = { ... }
```

### Import

```tao
// Import entire module
import math

// Import with alias
import math as m

// Import specific names
import math { min, max, abs }

// Import with alias
import math { min as mn, max }

// Import all names (not recommended)
import math *

// Import from nested module
import my_app/data/tree { Node, Leaf }
```

### Usage

```tao
// Qualified access
math.min(1, 2)
m.max(3, 4)

// Direct access after import
min(1, 2)
max(3, 4)

// After import *
abs(-5)
```

### Project Structure

```
my_project/
├── tao.json          # Project manifest
├── src/
│   ├── main.tao      # Entry point
│   ├── utils.tao     # Module: utils
│   └── data/
│       └── tree.tao  # Module: data/tree
└── lib/              # Third-party dependencies
```

---

## Learn Tao in Y Minutes

```tao
// ============================================================================
// 1. VARIABLES AND TYPES
// ============================================================================

let x = 42              // Inferred: Int (default I32)
let y: F64 = 3.14       // Explicit type
let mut counter = 0     // Mutable
counter = counter + 1

// ============================================================================
// 2. PRIMITIVE OPERATIONS
// ============================================================================

let a = 5 + 3           // Int: 8
let b = 5.0 + 3.0       // F64: 8.0
let eq = 5 == 5         // True (constructor)
let and = True && False // False

// ============================================================================
// 3. FUNCTIONS
// ============================================================================

// Basic function
fn add(a: Int, b: Int) -> Int {
  a + b
}

// Generic function (explicit type parameters)
fn identity<a>(x: a) -> a {
  x
}

fn map<a, b>(list: List(a), f: fn(a) -> b) -> List(b) {
  // Implementation
}

// Overloaded functions
fn add(a: Int, b: Int) -> Int { int_add(a, b) }
fn add(a: F64, b: F64) -> F64 { float_add(a, b) }

// ============================================================================
// 4. DATA STRUCTURES
// ============================================================================

// Record type
type Point = { x: F64, y: F64 }
let p = { x: 1.0, y: 2.0 }
let px = p.x

// Sum types (standard library)
type Maybe(a) = Some(a) | None
type Result(a, e) = Ok(a) | Err(e)

// GADT
type Vec(n: Int, a: Type) =
  | Nil: Vec(0, a)
  | Cons: (a, Vec(n, a)) -> Vec(n + 1, a)

// ============================================================================
// 5. PATTERN MATCHING
// ============================================================================

match maybe_val {
  | Some(x) -> x
  | None -> 0
}

fn classify(n: Int) -> String {
  match n {
    | x if x < 0 -> "negative"
    | x if x == 0 -> "zero"
    | x if x > 0 -> "positive"
  }
}

// ============================================================================
// 6. ERROR HANDLING
// ============================================================================

fn process() -> Result(Int, String) {
  let x <- parse_int("42")  // Bind operator
  let y <- parse_int("10")
  Ok(x + y)
}

let city = user?.address?.city  // Optional chaining
let value = result?             // Result unwrap

// ============================================================================
// 7. LISTS AND COLLECTIONS
// ============================================================================

let nums = [1, 2, 3, 4, 5]

let doubled = nums.map(fn(x) { x * 2 })
let evens = nums.filter(fn(x) { x % 2 == 0 })

// Pipe operator
let result = nums
  |> filter(fn(x) { x % 2 == 0 })
  |> map(fn(x) { x * 2 })
  |> fold(0, fn(acc, x) { acc + x })

// ============================================================================
// 8. DEPENDENT TYPES
// ============================================================================

type Matrix(rows: Int, cols: Int) = {
  data: List(List(F64)),
  shape: (rows, cols),
}

fn matmul(a: Matrix(m, n), b: Matrix(n, p)) -> Matrix(m, p) {
  // Type checker verifies dimensions
}

let a: Matrix(2, 3) = create_matrix(2, 3)
let b: Matrix(3, 4) = create_matrix(3, 4)
let c = matmul(a, b)  // Type: Matrix(2, 4)

// ============================================================================
// 9. ATTRIBUTES
// ============================================================================

@permission(Read("/tmp"))
fn read_temp() -> Result(String, Error) {
  read_file("/tmp/data.txt")
}

@effect(IO)
fn print(msg: String) -> Unit { }

@inline
fn fast_double(x: Int) -> Int { x * 2 }

// ============================================================================
// 10. COMPTIME
// ============================================================================

// Comptime expression
let x = comptime factorial(5)

// Comptime with block
let config = comptime do {
  let size = 1024
  load_config(size)
}

// Comptime function
@comptime
fn factorial(n: Int) -> Int {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let fact_5 = factorial(5)  // 120

// ============================================================================
// 11. MODULES
// ============================================================================

module my_app/main

import math as m { min, max }
import std/list *

// Public by default
fn helper() -> Unit { ... }

// Private (starts with _)
fn _internal() -> Unit { ... }

// ============================================================================
// 12. IMPERATIVE BLOCKS
// ============================================================================

let result = do {
  mut sum = 0
  mut i = 0
  while i < 10 {
    sum = sum + i
    i = i + 1
  }
  sum
}

// ============================================================================
// 13. COMPLETE EXAMPLE
// ============================================================================

type Expr =
  | Num(Int)
  | Add(Expr, Expr)
  | Div(Expr, Expr)

type EvalError = DivisionByZero

fn eval(expr: Expr) -> Result(F64, EvalError) {
  match expr {
    | Num(x) -> Ok(x)
    | Add(a, b) -> do {
        let x <- eval(a)
        let y <- eval(b)
        Ok(x + y)
      }
    | Div(a, b) -> do {
        let x <- eval(a)
        let y <- eval(b)
        if y == 0.0 {
          Err(DivisionByZero)
        } else {
          Ok(x / y)
        }
      }
  }
}

let expr = Div(Add(Num(10), Num(5)), Num(3))
let result = eval(expr)  // Ok(5.0)
```

---

## References

- [Tao Overview](./01-overview.md)
- [Desugaring Rules](./03-desugaring.md)
- [Syntax Library](../../syntax-library.md)
