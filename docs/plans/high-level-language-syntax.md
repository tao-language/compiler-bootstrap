# High-Level Language Syntax Proposal

> **Status**: Draft - For future iteration
> **Goal**: Familiar, TypeScript-like syntax for the high-level language
> **Important**: NOT object-oriented - uses TS syntax but functional semantics

---

## Design Principles

1. **TypeScript-like** - Familiar to most developers, LLMs have seen tons of TS
2. **Minimal boilerplate** - Type inference where possible
3. **Clear visual structure** - Indentation matters (like TS/JS)
4. **Explicit where it matters** - Type annotations when needed for clarity
5. **Pattern matching** - Rust/Swift-style, familiar and powerful
6. **Functional** - No objects, no classes, no inheritance, no mutation

---

## Why Not Object-Oriented?

**This language uses TypeScript-like syntax but is NOT object-oriented.**

### Problems with OO

| Issue | Why It Matters |
|-------|---------------|
| **Hidden complexity** | Method dispatch, virtual tables, dynamic binding |
| **Inheritance** | Fragile base class problem, diamond inheritance |
| **Mutable state** | Race conditions, hard to reason about |
| **Encapsulation** | Hides complexity instead of eliminating it |
| **`this` binding** | Confusing, context-dependent |
| **Side effects** | Hard to parallelize, distribute, or GPU-accelerate |

### Why Functional?

| Benefit | Why It Matters |
|---------|---------------|
| **Immutability** | Safe to share across threads/machines |
| **Pure functions** | Easy to parallelize and cache |
| **Explicit data flow** | Clear what depends on what |
| **Pattern matching** | Exhaustive, compiler-verified |
| **Type safety** | Catch errors at compile time |
| **Composability** | Functions compose naturally |
| **Distribution** | No hidden state, easy to serialize |
| **GPU-friendly** | No mutation, easy to vectorize |

### Design Principle

> **Syntax like TypeScript, Semantics like OCaml/Rust**
>
> - **Familiar syntax** - Easy to learn, LLM-friendly
> - **Functional semantics** - Safe, parallelizable, distributable
> - **No objects** - Just data and functions
> - **No classes** - Just types and functions
> - **No inheritance** - Just composition

---

## Syntax Overview

### 1. **Basic Structure**

```typescript
// Comments use // like TS/JS
/* Block comments too */

// Import syntax - TypeScript-like
import { List, Map } from "std/collections"
import * as io from "std/io"

// Constants (immutable by default)
const PI = 3.14159
const MAX_SIZE: Int = 100

// Variables (immutable with let, NO var for mutation)
let x = 42           // Inferred type
let y: Int = 42      // Explicit type
// NO: var counter = 0  -- No mutation!
```

### 2. **Functions (NOT Methods)**

```typescript
// Simple function with inferred return type
function add(a, b) {
  return a + b
}

// Explicit types
function add(a: Int, b: Int): Int {
  return a + b
}

// Multiple return values (tuple)
function divide(a: Int, b: Int): [Int, Int] {
  return [a / b, a % b]
}

// Generic function
function identity<T>(x: T): T {
  return x
}

// Function with default parameters
function greet(name: String = "World"): String {
  return "Hello, " + name
}

// Arrow function syntax (for lambdas)
const double = (x: Int): Int => x * 2

// Function type alias
type Comparator<T> = (a: T, b: T) => Int

// Functions are NOT methods - they don't belong to classes
// They're just functions that operate on data
```

### 3. **Types (NOT Classes)**

```typescript
// Type alias
type UserId = String
type Point = { x: Int, y: Int }

// Type definition (NOT a class!)
type Option<T> = 
  | { tag: "Some", value: T }
  | { tag: "None" }

type Result<T, E> =
  | { tag: "Ok", value: T }
  | { tag: "Err", error: E }

// Record type (just data, no methods!)
type Person = {
  name: String
  age: Int
  email?: String  // Optional field
}

// Enum/Union type (tagged union)
type Color = 
  | { tag: "Red" }
  | { tag: "Green" }
  | { tag: "Blue" }

// NO classes, NO methods on types
```

### 4. **Pattern Matching**

```typescript
// Match expression (Rust/Swift-like)
match (value) {
  case 0: return "zero",
  case 1: return "one",
  case n if n > 0: return "positive",
  case _: return "negative"  // Wildcard
}

// Destructuring
match (point) {
  case { x: 0, y: 0 }: return "origin",
  case { x, y }: return `point at (${x}, ${y})`
}

// Type matching
match (option) {
  case { tag: "Some", value }: return value,
  case { tag: "None" }: return defaultValue
}

// Guard clauses
match (user) {
  case { age } if age >= 18: return "adult",
  case _: return "minor"
}

// Nested patterns
match (tree) {
  case { tag: "Node", left: { tag: "Leaf", value: x }, right: { tag: "Leaf", value: y } }: 
    return x + y,
  case { tag: "Node", left, right }: 
    return eval(left) + eval(right),
  case { tag: "Leaf", value: n }: 
    return n
}
```

### 5. **Control Flow**

```typescript
// If expression (returns value)
const result = if (x > 0) {
  "positive"
} else if (x < 0) {
  "negative"
} else {
  "zero"
}

// For loop (functional style, no mutation)
for (const i of range(0, 10)) {
  io.print(i)
}

// For with destructuring
for (const { key, value } of map) {
  io.print(`${key}: ${value}`)
}

// While loop (rare, use recursion instead)
while (condition) {
  // ...
}

// NO: No loop variables that mutate
// Use recursion or functional combinators instead
```

### 6. **Records and Data (NOT Objects)**

```typescript
// Record literal (just data, no methods)
const config = {
  debug: true,
  maxRetries: 3,
  timeout: 5000
}

// Record with functions (data + separate functions)
const calculator = {
  add: (a: Int, b: Int): Int => a + b,
  subtract: (a: Int, b: Int): Int => a - b
}

// Access fields
config.debug
calculator.add(1, 2)

// Update record (immutable, creates new record)
const newConfig = { ...config, debug: false }

// NO: No methods on records
// NO: No `this` keyword
// NO: No prototype chain
```

### 7. **Modules and Exports**

```typescript
// Export
export function publicFunction() { }
export const PUBLIC_CONSTANT = 42
export type PublicType = { x: Int }

// Re-export
export { List, Map } from "std/collections"

// Module declaration
module MyModule {
  export function helper() { }
  
  // Private to module
  function internalHelper() { }
}
```

### 8. **Error Handling**

```typescript
// Try-catch-finally
try {
  riskyOperation()
} catch (e: Error) {
  io.print(`Error: ${e.message}`)
} finally {
  cleanup()
}

// Result type (Rust-like, NOT exceptions)
function divide(a: Int, b: Int): Result<Int, String> {
  if (b == 0) {
    return { tag: "Err", error: "Division by zero" }
  }
  return { tag: "Ok", value: a / b }
}

// Option type
function findUser(id: UserId): Option<User> {
  // ...
}

// Null coalescing
const name = user.name ?? "Anonymous"

// Optional chaining
const city = user?.address?.city
```

### 9. **Advanced Types**

```typescript
// Type constraints
function sort<T extends Ord>(items: Array<T>): Array<T> {
  // ...
}

// Union types
type Shape = Circle | Rectangle | Triangle

// Intersection types
type ColoredPoint = Point & { color: String }

// Mapped types
type Readonly<T> = {
  readonly [K in keyof T]: T[K]
}

// Conditional types
type Extract<T, U> = T extends U ? T : never
```

### 10. **Macros and Metaprogramming**

```typescript
// Simple macro
macro when(value, clauses...) {
  match (value) {
    clauses...
  }
}

// Usage
when (x) {
  case 0: return "zero",
  case 1: return "one",
  case _: return "other"
}

// Derive macro
@derive(Debug, Clone, Eq)
type Point = {
  x: Int,
  y: Int
}

// Compile-time evaluation
const FACTORIAL_5 = comptime {
  function fact(n: Int): Int {
    if (n <= 1) { return 1 }
    return n * fact(n - 1)
  }
  fact(5)
}
```

### 11. **Async/Await**

```typescript
// Async function
async function fetchData(url: String): Promise<Data> {
  const response = await fetch(url)
  return await response.json()
}

// Parallel execution
const [users, posts] = await Promise.all([
  fetchUsers(),
  fetchPosts()
])

// Async iteration
for await (const line of readLines(file)) {
  process(line)
}
```

### 12. **Type Annotations**

```typescript
// Type annotations
let x: Int = 42
const name: String = "Alice"
const items: Array<Int> = [1, 2, 3]
const map: Map<String, Int> = new Map()

// Function types
const fn: (a: Int, b: Int) => Int = add

// Generic types
const list: List<Option<Int>> = [
  { tag: "Some", value: 1 }, 
  { tag: "None" }, 
  { tag: "Some", value: 3 }
]

// Type assertions
const x = value as Int
const y = <Int>value

// Type queries
type T = typeof x
type Props = typeof Component.props
```

---

## Complete Example

```typescript
// Standard library imports
import { List, Option, Result } from "std/core"
import * as io from "std/io"

// Type definitions (NOT classes!)
type UserId = String

type User = {
  id: UserId
  name: String
  email: String
  age: Int
}

type AuthResult =
  | { tag: "Success", user: User }
  | { tag: "InvalidCredentials" }
  | { tag: "AccountLocked" }

// Main function
function main() {
  const users: List<User> = [
    { id: "1", name: "Alice", email: "alice@example.com", age: 30 },
    { id: "2", name: "Bob", email: "bob@example.com", age: 25 }
  ]
  
  // Pattern matching
  match (authenticate("alice@example.com", "password")) {
    case { tag: "Success", user }: {
      io.print(`Welcome, ${user.name}!`)
      showDashboard(user)
    },
    case { tag: "InvalidCredentials" }: {
      io.print("Invalid credentials")
      showLogin()
    },
    case { tag: "AccountLocked" }: {
      io.print("Account locked")
      showSupport()
    }
  }
  
  // Higher-order functions (NOT method chaining on objects)
  const adults = join(
    map(
      filter(users, (u: User): Bool => u.age >= 18),
      (u: User): String => u.name
    ),
    ", "
  )
  
  io.print(`Adults: ${adults}`)
}

// Function with explicit types (NOT a method!)
function authenticate(email: String, password: String): AuthResult {
  match (findUserByEmail(email)) {
    case { tag: "Some", value: user } if checkPassword(user, password): 
      return { tag: "Success", user: user },
    case { tag: "Some", value: _ }: 
      return { tag: "InvalidCredentials" },
    case { tag: "None" }: 
      return { tag: "InvalidCredentials" }
  }
}

// Generic function
function findUserByEmail(email: String): Option<User> {
  // Implementation...
  return { tag: "None" }
}

// Private helper (NOT a private method)
function checkPassword(user: User, password: String): Bool {
  // Implementation...
  return false
}

function showDashboard(user: User) {
  io.print(`Showing dashboard for ${user.name}`)
}

function showLogin() {
  io.print("Showing login form")
}

function showSupport() {
  io.print("Showing support contact")
}
```

---

## Key Design Decisions

| Feature | Choice | Rationale |
|---------|--------|-----------|
| **Comments** | `//` and `/* */` | Universal, familiar |
| **Blocks** | `{ }` with indentation | TS/JS standard |
| **Statements** | Semicolon optional | Modern TS style |
| **Functions** | `function` or `=>` | TS standard |
| **Types** | Postfix `: Type` | TS standard |
| **Generics** | `<T>` | TS/Java standard |
| **Pattern Match** | `match (x) { case ... }` | Rust/Swift hybrid |
| **Null** | `Option<T>` | No null references |
| **Errors** | `Result<T, E>` | Explicit error handling |
| **Async** | `async`/`await` | JS/TS standard |
| **Modules** | `import`/`export` | ES6/TS standard |
| **Classes** | **NOT SUPPORTED** | Functional only |
| **Inheritance** | **NOT SUPPORTED** | Composition only |
| **Mutation** | **NOT SUPPORTED** | Immutability only |
| **`this`** | **NOT SUPPORTED** | No objects |

---

## What Makes This LLM-Friendly?

1. **High training data** - Syntax matches TypeScript, which LLMs have seen extensively
2. **Unambiguous** - Clear token boundaries, no sigil overload
3. **Regular structure** - Consistent patterns throughout
4. **Explicit types** - When provided, types guide generation
5. **Pattern matching** - Structured, easy to complete correctly
6. **No magic** - What you see is what you get
7. **Functional semantics** - Easier to reason about than OO

---

## Comparison: High-Level vs Core

```typescript
// High-Level (TypeScript-like syntax, functional semantics)
function add(a: Int, b: Int): Int {
  return a + b
}

const result = match (opt) {
  case { tag: "Some", value }: value,
  case { tag: "None" }: 0
}

// Core (explicit, minimal syntax)
add(a: Int, b: Int): Int -> a + b

match opt {
| Some(value) -> value
| None -> 0
}
```

---

## Notes for Future Iteration

### Features to Potentially Simplify/Remove

1. **Classes** - Already removed, use types + functions
2. **Interface vs Type** - Maybe just use `type`
3. **Async/await** - May not be needed in initial version
4. **Generics syntax** - Could be simplified
5. **Optional chaining** - Nice but adds complexity
6. **Template strings** - Could use simple string concat
7. **Pipe operator** - Nice but not essential

### Questions to Resolve

1. Do we need both `function` and `=>`? Or just one?
2. Should pattern matching be an expression or statement?
3. Do we need type inference or always explicit?
4. What about modules - simple imports or full module system?
5. How much TS syntax to keep vs. simplify?

---

## Next Steps

1. Review and simplify the syntax
2. Remove overlapping features
3. Decide on minimal feature set
4. Create formal grammar
5. Implement lexer and parser
6. Compile to core language
