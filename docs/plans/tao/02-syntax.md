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
Some, None, Ok, Err
import, export, module, as
comptime, const
```

### Literals

```tao
42              // I32
42_i64          // I64
3.14            // F64
3.14_f32        // F32
"hello"         // String
"hello\nworld"  // With escape sequences
true, false     // Bool
```

### Identifiers

```tao
lowercase       // Variables, functions
snake_case      // Preferred for functions
Uppercase       // Types, constructors
PascalCase      // Preferred for types
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
.   ?.   ?   <-   |>   =   :   ->   =>
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

### Primitive Types

```tao
I32, I64, U32, U64    // Integers
F32, F64              // Floats
Bool                  // Boolean
String                // String
Unit                  // Unit type (like void)
```

### Type Variables

```tao
// Lowercase letters are type variables
fn id(a: a) -> a { a }
fn map(a: a, f: (a) -> b) -> b { f(a) }
```

### Generic Types

```tao
Maybe(a)
Result(a, e)
List(a)
Map(k, v)
Option(a)      // Alias for Maybe
```

### Dependent Types

```tao
// Type indexed by value
Vec(n: Nat, a: Type)
Matrix(rows: Nat, cols: Nat)
Array(size: I32, a: Type)

// Usage
type Vec3 = Vec(3, F64)
fn dot(a: Vec3, b: Vec3) -> F64 { ... }
```

---

## Variables and Bindings

### Immutable (Default)

```tao
let x = 5
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
// Mutable variables in a block (desugars to tail-recursive function)
let result = {
  mut sum = 0
  mut i = 0
  while i < 10 {
    sum = sum + i
    i = i + 1
  }
  sum  // Final expression is block value
}

// With early return
let found = {
  for x in list {
    if x == target { return Some(x) }
  }
  None
}

// For loop (desugars to fold/map)
let doubled = for x in [1, 2, 3] {
  x * 2
}
// Desugars to: list.map([1, 2, 3], fn(x) { x * 2 })
```

---

## Functions

### Basic Function

```tao
fn add(a: I32, b: I32) -> I32 {
  a + b
}
```

### Type Inference

```tao
// Parameters can omit types (inferred from usage)
fn multiply(a, b) { a * b }

// Return type can be omitted
fn greet(name: String) {
  "Hello, " <> name
}
```

### Generic Function

```tao
fn map(list: List(a), f: (a) -> b) -> List(b) {
  // Implementation
}

fn identity(x: a) -> a {
  x
}
```

### Overloaded Function

```tao
fn add(a: I32, b: I32) -> I32 { i32_add(a, b) }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }
fn add(a: String, b: String) -> String { string_concat(a, b) }

// Usage (type inference resolves overload)
let x = 1 + 2           // I32
let y = 1.0 + 2.0       // F64
let z = "a" + "b"       // "ab"
```

### Anonymous Function

```tao
let double = fn(x: I32) -> I32 { x * 2 }
let add = fn(a, b) { a + b }
```

---

## Types and Data

### Record Type

```tao
type Point = {
  x: F64,
  y: F64,
}

type Person = {
  name: String,
  age: I32,
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

### Sum Type (Enum)

```tao
type Maybe(a) {
  Some(a)
  None
}

type Result(a, e) {
  Ok(a)
  Err(e)
}

type List(a) {
  Nil
  Cons(a, List(a))
}
```

### GADT

```tao
type Vec(n: Nat, a: Type) {
  Nil: Vec(0, a)
  Cons: (n: Nat, a, Vec(n, a)) -> Vec(n + 1, a)
}

type Expr(t: Type) {
  Num: F64 -> Expr(F64)
  Add: (Expr(F64), Expr(F64)) -> Expr(F64)
  If: (Expr(Bool), Expr(t), Expr(t)) -> Expr(t)
}
```

---

## Pattern Matching

### Basic Match

```tao
match value {
  Some(x) => x
  None => 0
}
```

### With Guards

```tao
fn classify(n: I32) -> String {
  match n {
    x if x < 0 => "negative"
    x if x == 0 => "zero"
    x if x > 0 => "positive"
  }
}
```

### Nested Patterns

```tao
match list {
  Cons(head, Cons(second, Nil)) => Some(second)
  _ => None
}
```

### Record Patterns

```tao
match person {
  { name: "Alice", age: _ } => "Found Alice"
  { name: n, age: a } => n <> " is " <> a
}
```

### Or Patterns

```tao
match value {
  Some(0) | None => "zero or nothing"
  Some(x) => "something: " <> x
}
```

---

## Error Handling

### Result Type

```tao
type Result(a, e) {
  Ok(a)
  Err(e)
}
```

### Bind Operator (`<-`)

```tao
fn process() -> Result(I32, String) {
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
  Ok(x) => print(x)
  Err(e) => print("Error: " <> e)
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
  Some(x) => x
  None => default
}
```

### Early Return

```tao
fn find_positive(nums: List(I32)) -> Maybe(I32) {
  match nums {
    Nil => return None
    Cons(x, _) if x > 0 => return Some(x)
    Cons(_, xs) => find_positive(xs)
  }
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
fn random() -> I32 {
  // Uses random number generator
}
```

### Inline Attribute

```tao
@inline
fn fast_double(x: I32) -> I32 {
  x * 2
}
```

### Comptime Attribute

```tao
@comptime
fn factorial(n: I32) -> I32 {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let fact_5 = factorial(5)  // Evaluated at compile-time
```

---

## Modules

### Module Declaration

```tao
module my_module

export { public_fn, PublicType, public_var }
```

### Import

```tao
// Named imports
import list.{map, filter, fold, length}

// Import with alias
import io as file_io

// Import all (not recommended)
import result.*

// Import from nested module
import my_app/data/tree.{Node, Leaf}
```

### Usage

```tao
let len = list.length(nums)
let data = file_io.read("file.txt")
```

### Visibility

```tao
// Public (exported)
pub fn helper() -> Unit { ... }

// Private (default, internal to module)
fn internal() -> Unit { ... }
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

## Comptime

### Comptime Block

```tao
comptime {
  let size = 1024
  type Buffer = Array(size, I32)
}
```

### Comptime Function

```tao
const fn factorial(n: I32) -> I32 {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let x = factorial(5)  // Evaluated at compile-time: 120
```

### Comptime Evaluation

```tao
// Compile-time known values
const BUFFER_SIZE = 1024
const PI = 3.14159

// Used in types
type Buffer = Array(BUFFER_SIZE, I32)
```

---

## Learn Tao in Y Minutes

```tao
// ============================================================================
// LEARN TAO IN Y MINUTES
// ============================================================================

// ----------------------------------------------------------------------------
// 1. VARIABLES AND TYPES
// ----------------------------------------------------------------------------

let x = 42              // Inferred: I32
let y: F64 = 3.14       // Explicit type
let mut counter = 0     // Mutable
counter = counter + 1

// ----------------------------------------------------------------------------
// 2. PRIMITIVE OPERATIONS
// ----------------------------------------------------------------------------

let a = 5 + 3           // I32: 8
let b = 5.0 + 3.0       // F64: 8.0
let eq = 5 == 5         // true
let and = true && false // false

// ----------------------------------------------------------------------------
// 3. FUNCTIONS
// ----------------------------------------------------------------------------

fn add(a: I32, b: I32) -> I32 {
  a + b
}

fn multiply(a, b) { a * b }  // Types inferred

fn identity(x: a) -> a { x }  // Generic

// Overloaded
fn add(a: I32, b: I32) -> I32 { i32_add(a, b) }
fn add(a: F64, b: F64) -> F64 { f64_add(a, b) }

// ----------------------------------------------------------------------------
// 4. DATA STRUCTURES
// ----------------------------------------------------------------------------

type Point = { x: F64, y: F64 }
let p = { x: 1.0, y: 2.0 }
let px = p.x

type Maybe(a) { Some(a), None }
type Result(a, e) { Ok(a), Err(e) }

// GADT
type Vec(n: Nat, a: Type) {
  Nil: Vec(0, a)
  Cons: (n: Nat, a, Vec(n, a)) -> Vec(n + 1, a)
}

// ----------------------------------------------------------------------------
// 5. PATTERN MATCHING
// ----------------------------------------------------------------------------

match maybe_val {
  Some(x) => x
  None => 0
}

fn classify(n: I32) -> String {
  match n {
    x if x < 0 => "negative"
    x if x == 0 => "zero"
    x if x > 0 => "positive"
  }
}

// ----------------------------------------------------------------------------
// 6. ERROR HANDLING
// ----------------------------------------------------------------------------

fn process() -> Result(I32, String) {
  let x <- parse_int("42")  // Bind operator
  let y <- parse_int("10")
  Ok(x + y)
}

let city = user?.address?.city  // Optional chaining
let value = result?             // Result unwrap

// ----------------------------------------------------------------------------
// 7. LISTS AND COLLECTIONS
// ----------------------------------------------------------------------------

let nums = [1, 2, 3, 4, 5]

let doubled = nums.map(fn(x) { x * 2 })
let evens = nums.filter(fn(x) { x % 2 == 0 })

// Pipe operator
let result = nums
  |> filter(fn(x) { x % 2 == 0 })
  |> map(fn(x) { x * 2 })
  |> fold(0, fn(acc, x) { acc + x })

// ----------------------------------------------------------------------------
// 8. DEPENDENT TYPES
// ----------------------------------------------------------------------------

type Matrix(rows: Nat, cols: Nat) = {
  data: List(List(F64)),
  shape: (rows, cols),
}

fn matmul(a: Matrix(m, n), b: Matrix(n, p)) -> Matrix(m, p) {
  // Type checker verifies n matches
}

let a: Matrix(2, 3) = create_matrix(2, 3)
let b: Matrix(3, 4) = create_matrix(3, 4)
let c = matmul(a, b)  // Type: Matrix(2, 4)

// ----------------------------------------------------------------------------
// 9. ATTRIBUTES
// ----------------------------------------------------------------------------

@permission(Read("/tmp"))
fn read_temp() -> Result(String, Error) {
  read_file("/tmp/data.txt")
}

@effect(IO)
fn print(msg: String) -> Unit { }

@inline
fn fast_double(x: I32) -> I32 { x * 2 }

// ----------------------------------------------------------------------------
// 10. COMPTIME
// ----------------------------------------------------------------------------

comptime {
  let buffer_size = 1024
  type Buffer = Array(buffer_size, I32)
}

const fn factorial(n: I32) -> I32 {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}

let fact_5 = factorial(5)  // 120

// ----------------------------------------------------------------------------
// 11. COMPLETE EXAMPLE
// ----------------------------------------------------------------------------

type Expr {
  Num(F64)
  Add(Expr, Expr)
  Div(Expr, Expr)
}

type EvalError { DivisionByZero }

fn eval(expr: Expr) -> Result(F64, EvalError) {
  match expr {
    Num(x) => Ok(x)
    Add(a, b) => {
      let x <- eval(a)
      let y <- eval(b)
      Ok(x + y)
    }
    Div(a, b) => {
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
