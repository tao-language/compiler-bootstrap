# Core Language Syntax (5-Minute Guide)

> **Purpose**: Core is a dependently-typed **compilation target** for high-level languages like Tao
> **Design**: `%` for keywords, `#` for constructors, clean namespaces

---

## Quick Rules

| Prefix | Purpose | Examples |
|--------|---------|----------|
| `%` | Keywords (meta-operators) | `%let`, `%match`, `%call`, `%fix`, `%comptime`, `%def`, `%Type` |
| `#` | Constructors (data variants) | `#True`, `#False`, `#Nil`, `#Cons(x)` |
| (none) | Variables, types, operations | `x`, `add`, `i32_add`, `Maybe` |

**Why?** High-level languages can use `match`, `case`, `let` as keywords. Core keeps all names available for variables.

---

## 1. Comments

```text
// Single line comment

/* Multi-line
   comment */
```

---

## 2. Literals & Types

```text
42          // Integer literal (type: %I32)
3.14        // Float literal (type: %F64)
"hello"     // String literal

// Types use % prefix
%I32        // 32-bit integer type
%F64        // 64-bit float type
%Type       // Universe type (type of types)
```

**Type Annotation**:
```text
(x : %I32)   // x has type I32
```

---

## 3. Functions (Lambdas)

```text
// Identity function
x -> x

// With type annotation
(x : %I32) -> x

// Curried function (takes x, returns function that takes y)
x -> y -> x

// Pi type (dependent function - return type depends on input value)
(n : %I32) -> Vec(n, A)  // Returns vector of length n
```

---

## 4. Let Bindings

```text
// Simple let
%let x = 42

// With type annotation
%let x : %I32 = 42

// Let in expression
%let x = 5 in x + x
```

---

## 5. Operations (`%call`)

Core has **no infix operators**. Use `%call` for built-in operations:

```text
// Arithmetic (i32)
%call i32_add(x, y)   // x + y
%call i32_sub(x, y)   // x - y
%call i32_mul(x, y)   // x * y
%call i32_div(x, y)   // x / y

// Arithmetic (i64, u32, u64, f32, f64)
%call i64_add(x, y)
%call u32_add(x, y)
%call f64_add(x, y)

// Comparison
%call i32_eq(x, y)    // x == y
%call i32_lt(x, y)    // x < y
```

---

## 6. Pattern Matching (`%match`)

```text
%match arg ~ motive {
  | pattern -> body
  | pattern -> body
}
```

- **`arg`**: Value to match
- **`motive`**: `(input_type) -> return_type` - tells type checker what each case returns
- **`cases`**: Pattern → body pairs

**Example** (simple):
```text
%match opt {
  | #Some(x) -> x
  | #None -> 0
}
```

**Example** (dependent type with motive):
```text
%match v ~ (n : %I32) -> %Type {
  | #Nil -> %I32
  | #Cons(k, x) -> Vec(k, A)
}
```

**Patterns**:
```text
_              // Wildcard (matches anything)
#Some(x)       // Constructor pattern
x if x > 0     // Guard (conditional match)
```

---

## 7. Recursion (`%fix`)

```text
// Factorial using fixpoint
%fix fact = \n -> %match n {
  | #Zero -> 1
  | _ -> %call i32_mul(n, fact(%call i32_sub(n, 1)))
}
```

**Syntax**: `%fix name = term`

---

## 8. Compile-Time Evaluation (`%comptime`)

```text
// Evaluate at compile-time
%comptime fact(5)  // Evaluates to 120

// In type position
%let v : Vec(%comptime { 2 + 3 }, %I32)  // Vec(5, %I32)
```

---

## 9. Constructors (`#`)

Constructors are **defined individually** (no type definition sugar):

```text
// Boolean type
%def #Bool -> %Type
%def #True -> #Bool
%def #False -> #Bool

// Option type (polymorphic)
%def #Maybe<a>(a) -> %Type
%def #Some<a>(a) -> #Maybe(a)
%def #None<a> -> #Maybe(a)

// Vector (dependent type - length is a value)
%def #Vec(n : %I32, a) -> %Type
%def #Nil<a> -> #Vec(0, a)
%def #Cons<a>(n : %I32, x : a) -> #Vec(%call i32_add(n, 1), a)
```

**Usage**:
```text
%let b = #True
%let opt = #Some(42)
%let v = #Cons(2, #Cons(1, #Nil))
```

---

## 10. Complete Example: Factorial

```text
// Factorial function using %I32
%fix fact = \n -> %match n {
  | #Zero -> 1
  | _ -> %call i32_mul(n, fact(%call i32_sub(n, 1)))
}

// Usage: Calculate factorial of 5
%let result = %comptime fact(5) in result

// With type annotation
%let result : %I32 = %comptime fact(5)
```

---

## 11. Complete Example: Vectors

```text
// Define vector constructors
%def #Vec(n : %I32, a) -> %Type
%def #Nil<a> -> #Vec(0, a)
%def #Cons<a>(n : %I32, x : a) -> #Vec(%call i32_add(n, 1), a)

// Create a vector
%let v = #Cons(2, #Cons(1, #Nil))

// Vector length
%fix vec_len = \v -> %match v ~ (n : %I32) -> %Type {
  | #Nil -> 0
  | #Cons(k, _) -> %call i32_add(k, 1)
}

// Usage
%let len = %comptime vec_len(v)  // 3
```

---

## 12. Universe Hierarchy

```text
%Type        // Alias for %Type(0) - type of values
%Type(0)     // Type of %I32, %F64, etc.
%Type(1)     // Type of %Type(0)
%Type(2)     // Type of %Type(1)

// Cumulativity
%Type(0) : %Type(1)
%Type(1) : %Type(2)
```

---

## 13. Holes (Metavariables)

```text
?      // Anonymous hole (to be solved)
?1     // Named hole (id = 1)
?2     // Named hole (id = 2)

// Usage (during development)
%let add = (x : %I32) -> (y : %I32) -> ?
```

---

## 14. Application

```text
// Function application (C-style only)
f(x)
add(5, 10)
fact(5)

// No infix application (f x not supported)
```

---

## Quick Reference

| Feature | Syntax | Example |
|---------|--------|---------|
| **Keyword** | `%name` | `%let`, `%match`, `%call` |
| **Constructor** | `#Name` | `#True`, `#Some(x)` |
| **Type** | `%Name` | `%I32`, `%Type`, `%F64` |
| **Lambda** | `x -> body` | `x -> x + 1` |
| **Pi Type** | `(x : A) -> B` | `(n : %I32) -> Vec(n)` |
| **Let** | `%let x = e` | `%let x = 42` |
| **Match** | `%match arg ~ motive { \| p -> b }` | `%match opt { \| #Some(x) -> x }` |
| **Fix** | `%fix name = term` | `%fix f = \n -> f(n-1)` |
| **Comptime** | `%comptime e` | `%comptime fact(5)` |
| **Call** | `%call op(args)` | `%call i32_add(x, y)` |
| **Hole** | `?` or `?1` | `let x = ?` |

---

## Key Concepts

### Why `%` Prefix?
Core is a **compilation target**. High-level languages define their own keywords:
- Tao: `match`, `case`, `let`
- Other language: `switch`, `case`, `val`

By using `%match`, `%let`, etc., Core keeps `match`, `let`, `case` available as variable names.

### Why `#` for Constructors?
Separates data constructors from variables and operations:
- `#Some(x)` - Constructor (data)
- `some(x)` - Function call (operation)
- `Some` - Type name (type)

### Dependent Types
Types that depend on **values**:
```text
(n : %I32) -> Vec(n, A)  // Type includes length value
```

### Motives
The motive in `%match` specifies the **return type** for each case (essential for GADTs):
```text
%match v ~ (n : %I32) -> %Type {
  | #Nil -> %I32           // This case returns %I32
  | #Cons(k, _) -> Vec(k)  // This case returns Vec(k)
}
```

---

## Built-in Operations

### Integer (i32, i64, u32, u64)
```text
%call i32_add(x, y)   // Addition
%call i32_sub(x, y)   // Subtraction
%call i32_mul(x, y)   // Multiplication
%call i32_div(x, y)   // Division
%call i32_eq(x, y)    // Equality
%call i32_lt(x, y)    // Less than
%call i32_gt(x, y)    // Greater than
```

### Float (f32, f64)
```text
%call f64_add(x, y)
%call f64_sub(x, y)
%call f64_mul(x, y)
%call f64_div(x, y)
%call f64_pow(x, y)   // Power
```

---

## Error Recovery

Core reports **all errors** in a single pass:
```text
// Multiple errors reported together
%let x : %I32 = "hello"  // Type mismatch
%let y = undefined       // Undefined variable
%match z { }             // Missing cases
```

---

## Related Documents

- **[docs/core.md](./core.md)** - Complete core language specification
- **[docs/syntax-library.md](./syntax-library.md)** - Syntax library documentation

---

## References

- [Core Implementation](../src/core/core.gleam)
- [Core Syntax](../src/core/syntax.gleam)
