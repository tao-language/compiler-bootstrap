# Core Language Syntax Quick Reference (Dependent Types)

Core is a dependently-typed target language. It uses `%` for keywords, `#` for constructors, and `%call` for operations to keep the namespace clean.

## 1. Philosophy & Rules
*   **Keywords** start with `%` (e.g., `%let`, `%match`).
*   **Constructors** start with `#` (e.g., `#True`, `#Nil`).
*   **No Infix Operators**: Use `%call` for all operations (e.g., `%call i32_add(x, y)`).
*   **No `$` Prefix**: Use `%Type` for universes and literal names (e.g., `%I32`) for types.

## 2. Comments
```text
// Single line comment
/* Multi-line comment */
```

## 3. Literals & Types
Literals are values; types describe their structure. Use `%Type` for universes and literal names (e.g., `%I32`, `%U32`) for types.

```text
42          // Integer literal (Type: %I32)
#True       // Constructor value (Type: %Type)
(x : %I32)   // Type annotation
```

## 4. Functions & Patterns (`->`)
Functions are lambdas (`x -> body`). This is syntactic sugar for dependent function types (Pi-types).

```text
x -> x       // Identity function
(x : %I32) -> x   // Explicitly typed lambda

// Pi Type (Dependent Function)
(x : A) -> B   // Return type depends on input value x
```

## 5. Pattern Matching (`%match`)
Pattern matching deconstructs values. The **motive** specifies the return type for each case, which is crucial for dependent types (GADTs).

```text
%match arg ~ motive { cases }
```

*   **`arg`**: The value to match.
*   **`motive`**: A function `(input_type) -> return_type`. Tells the checker what type each case returns.
*   **`cases`**: `| pattern -> body`.

**Example:**
```text
%match n ~ (k : %I32) -> %Type {
  | #Zero -> k        // Returns type k (depends on n)
  | _      -> %Type   // Returns universe type
}
```

## 6. Operations (`%call`)
Core has no infix operators like `+`. Use `%call` for built-in functions.

```text
%call i32_add(x, y)   // Addition (returns %I32)
%call i32_eq(x, y)    // Equality check (returns Bool)
```

## 7. Recursion (`%fix`) & Comptime (`%comptime`)
*   **Recursion**: `%fix name = term`. Defines a recursive function.
*   **Comptime**: `%comptime term`. Evaluates at compile-time (folds constants).

```text
%fix fact = \n -> match n with ...
%comptime 2 + 3       // Evaluates to 5 at compile-time
```

## 8. Factorial Implementation (`%I32`)
Here is a recursive factorial function using the `%I32` type. Note the use of `%call i32_...` operators and `%fix` for recursion.

```text
// Define factorial function
%fix fact = \n -> match n with
  | #Zero -> 1
  | _     -> %call i32_mul(n, fact(%call i32_sub(n, 1)))

// Usage: Calculate factorial of 5
%let result = %comptime fact(5) in result

// Type annotation (Optional but recommended)
result : %I32
```

## 9. Dependent Types Example: `Vec`
Vectors in Core are dependent types where the length is a value. To define `Vec`, use `%U32` for the universe level and `%call u32_add` to calculate length.

### Defining `Vec`
```text
// Define Nil constructor (Length must be 0)
%def #Nil : Vec(0, A)

// Define Cons constructor (Length becomes n + 1)
%def #Cons(n : %U32, x) -> Vec(%call u32_add(n, 1), A)
```

### Using `Vec`
```text
// Create a vector of length 2 containing 10 and 20
%let v = #Cons(2, %call i32_add(10, 20))

// Access head of vector (if length > 0)
%match v ~ (n : %U32, A) -> %Type {
  | #Nil -> %call i32_sub(0, n)   // Error: Length must be 0
  | #Cons(n, x) -> x              // Returns element type A
}
```

## 10. Quick Syntax Cheat Sheet

| Feature | Syntax | Description |
| :--- | :--- | :--- |
| **Comment** | `//` or `/* */` | Ignored by parser |
| **Literal** | `42`, `3.14` | Integer or Float value |
| **Constructor** | `#Name(args)` | Data variant (starts with #) |
| **Keyword** | `%let`, `%match` | Meta-operators (start with %) |
| **Lambda** | `x -> body` | Function definition |
| **FFI Call** | `%call i32_add(x, y)` | Built-in function call |
| **Recursion** | `%fix name = term` | Recursive definition |

## 11. Key Concepts Explained

### Dependent Types (Pi Types)
A function type `(x : A) -> B` where `B` can depend on the value of `x`.
```text
(x : %I32) -> Vec(x, Bool)   // Returns a vector of length x
```

### Motives (in `%match`)
The motive `(input_type) -> return_type` tells the type checker what type each branch returns. This is essential for GADTs where constructors return different types based on the input value.
```text
%match v ~ (n : %U32) -> %Type {
  | #Nil -> Vec(0, A)   // Case returns type Vec(0, A)
  | #Cons(n, x) -> Vec(Succ(n), A) // Case returns type Vec(Succ(n), A)
}
```

### Constructors (`#`) vs Keywords (`%`)
*   **Constructors** (`#Name`) are values that represent data variants. They must be defined individually using `%def`.
*   **Keywords** (`%Name`) are meta-operators used for language structure (e.g., `%match`, `%fix`).

### Error Recovery
Core reports all errors in a single pass. If an error occurs, checking continues to report other issues (e.g., type mismatches and missing match cases).
