# Error Types Specification

> **Goal**: Define rich error types that carry maximum context for helpful error messages
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Overview

This document specifies the error types for the compiler. Each error type includes:
- **Fields** - Data carried by the error
- **Spans** - Source locations to highlight
- **Message** - Human-readable description
- **Suggestions** - Actionable fixes

---

## Parse Errors

### E0001: UnexpectedToken

```gleam
pub type UnexpectedToken {
  UnexpectedToken(
    expected: String,      // What was expected
    got: String,           // What was found
    span: Span,            // Location of unexpected token
    context: String,       // What rule was being parsed
  )
}
```

**Example Output:**
```
error[E0001]: Unexpected token
   ┌─ src/example.core.tao:2:15
   │
 2 │ %match x ~ $Type { | y -> }
   │                         ^
   │
   = expected: expression
   = got:      '}'
   │
   = note: Every case must have a body
   = help: Add an expression after '->':
           | y -> <expression>
```

### E0002: MissingToken

```gleam
pub type MissingToken {
  MissingToken(
    expected: String,      // What token is missing
    span: Span,            // Where it should be
    context: String,       // What rule requires it
  )
}
```

**Example Output:**
```
error[E0002]: Missing token
   ┌─ src/example.core.tao:1:12
   │
 1 │ (x : $Type -> x
   │            ^
   │
   = expected: ')'
   │
   = note: Parenthesized type annotations must be closed
   = help: Add ')' after the type:
           (x : $Type) -> x
```

### E0003: InvalidSyntax

```gleam
pub type InvalidSyntax {
  InvalidSyntax(
    message: String,     // What's wrong
    span: Span,          // Location of error
    suggestion: String,  // How to fix it
  )
}
```

---

## Type Errors

### E0101: TypeMismatch

```gleam
pub type TypeMismatch {
  TypeMismatch(
    expected: Type,      // Expected type (normalized)
    got: Type,           // Actual type (normalized)
    expected_span: Span, // Where expected type appears
    got_span: Span,      // Where actual type appears
    context: String,     // What operation caused mismatch
  )
}
```

**Example Output:**
```
error[E0101]: Type mismatch
   ┌─ src/example.core.tao:3:5
   │
 3 │ let f = (x : $I32) -> x
   │           ^^^^^^^
   │
   = expected: $Type
   = got:      $I32
   │
   = note: Function parameter types must be $Type
   = hint: Use $Type for type-level computation:
           (x : $Type) -> x
```

### E0102: VarUndefined

```gleam
pub type VarUndefined {
  VarUndefined(
    name: String,        // Variable name (resolved from index)
    span: Span,          // Where undefined var appears
    scope: Scope,        // Current scope info
    similar: List(String), // Similar names in scope
  )
}
```

**Example Output:**
```
error[E0102]: Undefined variable
   ┌─ src/example.core.tao:1:8
   │
 1 │ x -> y
   │        ^
   │
   = 'y' is not defined
   │
   = note: Available variables:
           - x
   = help: Did you mean 'x'?
```

### E0103: NotAFunction

```gleam
pub type NotAFunction {
  NotAFunction(
    term: Term,          // The non-function term
    term_ty: Type,       // Its actual type
    span: Span,          // Application site
    arg_span: Span,      // Argument span
  )
}
```

**Example Output:**
```
error[E0103]: Not a function
   ┌─ src/example.core.tao:2:5
   │
 2 │ 42(x)
   │ ^^^^
   │
   = cannot apply: 42
   = type:         $I32
   │
   = note: Only functions can be applied
   = help: Remove the application or use a function:
           f(x) instead of 42(x)
```

### E0104: ArityMismatch

```gleam
pub type ArityMismatch {
  ArityMismatch(
    expected: Int,       // Expected argument count
    got: Int,            // Actual argument count
    span: Span,          // Application site
    name: String,        // Function name (if known)
  )
}
```

**Example Output:**
```
error[E0104]: Arity mismatch
   ┌─ src/example.core.tao:1:8
   │
 1 │ f(x, y)
   │ ^^^^^^^
   │
   = expected: 1 argument
   = got:      2 arguments
   │
   = note: Function 'f' has type (a : $Type) -> a
   = help: Remove the extra argument:
           f(x)
```

### E0105: InfiniteType

```gleam
pub type InfiniteType {
  InfiniteType(
    hole_id: Int,        // Metavariable being solved
    ty: Type,            // Type that would be infinite
    span: Span,          // Where unification happens
  )
}
```

**Example Output:**
```
error[E0105]: Infinite type
   ┌─ src/example.core.tao:1:1
   │
 1 │ (x : x) -> x
   │ ^^^^^^^
   │
   = cannot unify ?0 with (?0 -> ?0)
   │
   = note: This would create an infinite type
   = help: Add a type annotation to break the cycle:
           (x : $Type) -> x
```

### E0106: HoleUnsolved

```gleam
pub type HoleUnsolved {
  HoleUnsolved(
    id: Int,             // Hole identifier
    span: Span,          // Where hole appears
    expected_ty: Type,   // Expected type of hole
  )
}
```

**Example Output:**
```
error[E0106]: Unsolved hole
   ┌─ src/example.core.tao:1:5
   │
 1 │ x -> ?
   │     ^
   │
   = cannot solve metavariable ?0
   = expected type: $Type
   │
   = note: All holes must be solved during type checking
   = help: Replace with a value of type $Type:
           x -> $Type
```

---

## Pattern Match Errors

### E0201: MatchMissingCase

```gleam
pub type MatchMissingCase {
  MatchMissingCase(
    missing: Pattern,    // Missing pattern
    match_span: Span,    // Full match expression
    type_constructors: List(String), // All constructors
    covered: List(String), // Already covered
  )
}
```

**Example Output:**
```
error[E0201]: Missing pattern case
   ┌─ src/example.core.tao:3:1
   │
 3 │ %match opt ~ $Type {
   │ ^^^^^^^^^^^^^^^^^^^^
 4 │   | #Some(x) -> x
   │   ───────────────
 5 │ }
   │ ─
   │
   = missing: #None
   │
   = note: Type 'Option' has these constructors:
           - #Some (covered)
           - #None (missing)
   = help: Add the missing case:
           | #None -> <default_value>
```

### E0202: MatchRedundantCase

```gleam
pub type MatchRedundantCase {
  MatchRedundantCase(
    pattern: Pattern,    // Redundant pattern
    span: Span,          // Location of redundant case
    covered_by: Pattern, // Earlier pattern that covers it
  )
}
```

**Example Output:**
```
error[E0202]: Redundant pattern case
   ┌─ src/example.core.tao:5:3
   │
 5 │   | _ -> 0
   │     ^
 6 │   | y -> y
   │     ────
   │
   = this pattern is never matched
   = note: Already covered by '_' on line 5
   = help: Remove the redundant case or reorder patterns
```

### E0203: PatternMismatch

```gleam
pub type PatternMismatch {
  PatternMismatch(
    pattern: Pattern,    // The problematic pattern
    expected_ty: Type,   // Expected type
    pattern_ty: Type,    // Pattern's type
    pattern_span: Span,  // Pattern location
    expected_span: Span, // Where type was expected
  )
}
```

---

## Runtime Errors

### E0301: ComptimePermissionDenied

```gleam
pub type ComptimePermissionDenied {
  ComptimePermissionDenied(
    operation: String,   // What operation was attempted
    span: Span,          // Where in source
    required: List(Permission), // What permission needed
  )
}
```

**Example Output:**
```
error[E0301]: Permission denied
   ┌─ src/example.core.tao:1:1
   │
 1 │ %comptime %call prim.read_file("secret.txt")
   │ ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   │
   = cannot read file at compile time
   │
   = note: Comptime file access requires permission
   = help: Add permission flag or move to runtime:
           gleam run --allow-read=secret.txt
```

### E0302: DivisionByZero

```gleam
pub type DivisionByZero {
  DivisionByZero(
    span: Span,          // Where division occurs
    divisor: Term,       // The divisor expression
  )
}
```

---

## Error Context

Each error should optionally include:

```gleam
pub type ErrorContext {
  ErrorContext(
    note: Option(String),      // Additional context
    help: Option(String),      // How to fix
    see_also: List(String),    // Related errors
    url: Option(String),       // Documentation link
  )
}
```

---

## Error Codes

| Range | Category |
|-------|----------|
| E0001-E0099 | Parse errors |
| E0101-E0199 | Type errors |
| E0201-E0299 | Pattern match errors |
| E0301-E0399 | Runtime errors |
| E0401-E0499 | FFI errors |
| E0501-E0599 | Exhaustiveness errors |

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration

---

## Implementation Checklist

- [ ] Update `core/core.gleam` Error type with rich fields
- [ ] Add error codes to all error constructors
- [ ] Implement `error_to_diagnostic()` function
- [ ] Add suggestion generation for common errors
- [ ] Create error documentation pages for each code
- [ ] Add golden file tests for each error type
