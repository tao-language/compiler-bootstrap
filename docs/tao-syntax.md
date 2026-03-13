# Tao Language Syntax (5-Minute Guide)

> **Purpose**: Tao is a high-level **source language** that compiles to Core
> **Design**: TypeScript-like syntax, familiar to web developers
> **Status**: ✅ MVP Complete - Expressions with arithmetic and precedence

---

## Quick Rules

| Feature | Syntax | Examples |
|---------|--------|----------|
| **Keywords** | Plain words | `fn`, `let`, `match`, `if`, `else`, `type` |
| **Operators** | Infix | `+`, `-`, `*`, `/`, `==`, `!=` |
| **Variables** | Lowercase | `x`, `count`, `myVar` |
| **Types** | PascalCase | `Int`, `String`, `MyType` |
| **Functions** | `fn` keyword | `fn add(x, y) { x + y }` |

**Why?** Tao uses familiar syntax so you can write code that looks like TypeScript or JavaScript.

---

## 1. Comments

```tao
// Single line comment

/* Multi-line
   comment */
```

---

## 2. Literals & Types

```tao
42          // Integer literal
3.14        // Float literal
"hello"     // String literal
true        // Boolean true
false       // Boolean false
```

**Type Annotation** (optional in MVP):
```tao
let x: Int = 42
```

---

## 3. Expressions (MVP)

### Numbers

```tao
42
3.14
```

### Variables

```tao
x
count
myVariable
```

### Arithmetic Operators

```tao
// Addition
1 + 2

// Subtraction
10 - 5

// Multiplication
3 * 4

// Division
20 / 4
```

### Operator Precedence

```tao
// * and / bind tighter than + and -
1 + 2 * 3      // Parses as: 1 + (2 * 3) = 7
(1 + 2) * 3    // Parses as: (1 + 2) * 3 = 9

// Left-to-right associativity
10 - 5 - 2     // Parses as: (10 - 5) - 2 = 3
```

---

## 4. Parentheses

Use parentheses to override default precedence:

```tao
// Force addition before multiplication
(1 + 2) * 3    // = 9

// Nested parentheses
((1 + 2) * 3) / 4
```

---

## 5. Complete Examples

### Simple Arithmetic

```tao
// Add two numbers
1 + 2

// Complex expression
1 + 2 * 3 - 4 / 2
```

### Using Variables

```tao
// Variable reference
x

// Variable in expression
x + 5
```

### Precedence Examples

```tao
// Multiplication before addition
let result = 1 + 2 * 3  // result = 7

// Parentheses change order
let result = (1 + 2) * 3  // result = 9
```

---

## 6. Syntax Cheat Sheet

| Feature | Syntax | Example |
|---------|--------|---------|
| **Number** | literal | `42`, `3.14` |
| **Variable** | identifier | `x`, `count` |
| **Addition** | `+` | `1 + 2` |
| **Subtraction** | `-` | `10 - 5` |
| **Multiplication** | `*` | `3 * 4` |
| **Division** | `/` | `20 / 4` |
| **Parentheses** | `( )` | `(1 + 2) * 3` |
| **Comment** | `//` or `/* */` | `// comment` |

---

## 7. Key Concepts

### Infix Operators

Unlike Core (which uses `%call i32_add(x, y)`), Tao uses familiar infix syntax:

```tao
// Tao (high-level)
x + y

// Compiles to Core (low-level)
%call i32_add(x, y)
```

### Operator Precedence

Tao follows standard mathematical precedence:

1. **Highest**: `*`, `/` (multiplication, division)
2. **Lowest**: `+`, `-` (addition, subtraction)

```tao
// This:
1 + 2 * 3

// Is equivalent to:
1 + (2 * 3)

// Not:
(1 + 2) * 3
```

### Left Associativity

Operators of the same precedence group left-to-right:

```tao
// This:
10 - 5 - 2

// Is equivalent to:
(10 - 5) - 2  // = 3

// Not:
10 - (5 - 2)  // = 7
```

---

## 8. What's Next? (Future Features)

The MVP supports expressions only. Future versions will add:

### Function Calls
```tao
// Not yet in MVP
add(1, 2)
max(x, y)
```

### Let Bindings
```tao
// Not yet in MVP
let x = 5
let y: Int = 10
```

### Function Definitions
```tao
// Not yet in MVP
fn add(x, y) {
  x + y
}

fn factorial(n: Int): Int {
  if n <= 1 { 1 } else { n * factorial(n - 1) }
}
```

### Pattern Matching
```tao
// Not yet in MVP
match opt {
  | Some(x) -> x
  | None -> 0
}
```

---

## 9. Comparison: Tao vs Core

| Feature | Tao (High-Level) | Core (Low-Level) |
|---------|------------------|------------------|
| **Operators** | `x + y` | `%call i32_add(x, y)` |
| **Keywords** | `fn`, `let`, `match` | `%fn`, `%let`, `%match` |
| **Types** | `Int`, `String` | `%I32`, `%Type` |
| **Constructors** | `Some(x)`, `None` | `#Some(x)`, `#None` |
| **Purpose** | Human-readable source | Compilation target |

---

## 10. Related Documents

- **[docs/core-syntax.md](./core-syntax.md)** - Core language syntax (compilation target)
- **[docs/plans/tao/09-tao-mvp-plan.md](./plans/tao/09-tao-mvp-plan.md)** - Tao MVP implementation plan
- **[docs/plans/tao/01-overview.md](./plans/tao/01-overview.md)** - Tao language overview
- **[docs/syntax-library.md](./syntax-library.md)** - Syntax library documentation

---

## References

- [Tao Lexer](../src/tao/lexer.gleam)
- [Tao Syntax](../src/tao/syntax.gleam)
- [Tao Tests](../test/tao/syntax_test.gleam)
- [Core Language](../src/core/core.gleam)

---

**Tao provides a familiar, TypeScript-like syntax that compiles to the dependently-typed Core language.** 🚀
