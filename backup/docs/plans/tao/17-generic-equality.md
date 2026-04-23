# Generic Equality for ADTs

> **Goal**: Implement structural equality for user-defined algebraic data types
> **Status**: 📋 **Planned** - Not started
> **Date**: March 2026
> **Priority**: Medium - Enables ergonomic comparison for custom types

---

## Overview

**Problem**: Currently, `==` and `!=` must be manually implemented for each ADT:

```tao
type Point = Point(I32, I32)

// Manual implementation (tedious!)
fn (==)(a: Point, b: Point) -> Bool {
  match a {
    | Point(x1, y1) -> {
      match b {
        | Point(x2, y2) -> x1 == x2 && y1 == y2
      }
    }
  }
}
```

**Goal**: Automatic structural equality for all ADTs:

```tao
type Point = Point(I32, I32)

// Works automatically!
> Point(1, 2) == Point(1, 2)
True

> Point(1, 2) == Point(3, 4)
False
```

---

## Design Options

### Option 1: Default Generic Implementation

Provide a built-in generic equality function that works for all types:

```tao
// Built-in generic equality
fn (==)<a>(x: a, y: a) -> Bool {
  // Core provides structural equality via FFI
  %call structural_eq(x, y)
}
```

**Pros**:
- ✅ Simple for users (works automatically)
- ✅ Consistent behavior across all types
- ✅ No boilerplate

**Cons**:
- ❌ Can't customize equality per type
- ❌ May not work for types with function fields
- ❌ Requires Core FFI support for structural equality

---

### Option 2: Type Class / Trait System

Use a type class approach (like Haskell's `Eq`):

```tao
// Type class definition
trait Eq(a) {
  fn (==)(x: a, y: a) -> Bool
  fn (!=)(x: a, y: a) -> Bool { not(x == y) }  // Default implementation
}

// Instance for Bool
impl Eq(Bool) {
  fn (==)(a: Bool, b: Bool) -> Bool {
    match (a, b) {
      | (True, True) -> True
      | (False, False) -> True
      | _ -> False
    }
  }
}

// Instance for Point (manual)
type Point = Point(I32, I32)

impl Eq(Point) {
  fn (==)(a: Point, b: Point) -> Bool {
    match (a, b) {
      | (Point(x1, y1), Point(x2, y2)) -> x1 == x2 && y1 == y2
    }
  }
}

// Generic function using type class
fn contains<a: Eq>(list: List(a), item: a) -> Bool {
  match list {
    | Nil -> False
    | Cons(x, xs) -> x == item || contains(xs, item)
  }
}
```

**Pros**:
- ✅ Customizable per type
- ✅ Works with function fields (if type doesn't implement `Eq`)
- ✅ Type-safe (can't compare non-Eq types)

**Cons**:
- ❌ Boilerplate for each type
- ❌ Requires trait system implementation
- ❌ More complex for beginners

---

### Option 3: Derive Mechanism

Automatic derivation with opt-out:

```tao
// Derive equality automatically
#[derive(Eq)]
type Point = Point(I32, I32)

// Works automatically
> Point(1, 2) == Point(1, 2)
True

// Manual override if needed
type Custom = Custom(I32)

impl Eq(Custom) {
  // Custom equality logic
  fn (==)(a: Custom, b: Custom) -> Bool { ... }
}
```

**Pros**:
- ✅ Best of both worlds (auto + customizable)
- ✅ Clear intent (`#[derive(Eq)]`)
- ✅ Familiar to Rust/Haskell users

**Cons**:
- ❌ Requires derive macro system
- ❌ More compiler complexity
- ❌ Need to handle non-derivable cases (functions, etc.)

---

### Option 4: Core-Level Structural Equality

Leverage Core's built-in structural equality:

```tao
// Core already has structural equality via normalization
// Two terms are equal if they normalize to the same value

// Tao exposes this via a generic operator
fn (==)<a>(x: a, y: a) -> Bool {
  // Core normalizes both and compares
  %call core_structural_eq(x, y)
}
```

**How it works in Core**:

```gleam
// Core equality via normalization
fn structural_eq(s: State, v1: Value, v2: Value) -> Bool {
  // Normalize both values
  let norm1 = normalize(s.ffi, [], v1, span)
  let norm2 = normalize(s.ffi, [], v2, span)
  
  // Compare normalized terms structurally
  terms_equal(norm1, norm2)
}
```

**Pros**:
- ✅ No user boilerplate
- ✅ Works for all ADTs automatically
- ✅ Leverages existing Core functionality
- ✅ Consistent with dependent type theory

**Cons**:
- ❌ May be slow for complex types (normalization)
- ❌ Can't customize per type
- ❌ May not terminate for recursive types

---

## Recommended Approach: Option 4 + Option 2 Hybrid

**Phase 1**: Implement Core-level structural equality (Option 4)
- Works for all ADTs automatically
- No user boilerplate
- Tests Core's normalization

**Phase 2**: Add trait system for customization (Option 2)
- Allow custom equality when needed
- Support generic functions with constraints

---

## Implementation Plan

### Phase 1: Core Structural Equality

#### Step 1: Core FFI Builtin

Add structural equality to Core's FFI:

```gleam
// src/core/core.gleam

/// Structural equality via normalization
fn structural_eq(ffi: FFI, env: Env, args: List(Value), span: Span) -> Value {
  case args {
    [v1, v2] -> {
      // Normalize both values
      let norm1 = normalize(ffi, env, v1, span)
      let norm2 = normalize(ffi, env, v2, span)
      
      // Compare structurally
      if terms_equal(norm1, norm2) {
        VCtr("True", [])
      } else {
        VCtr("False", [])
      }
    }
    _ -> VErr
  }
}

/// Structural comparison of normalized terms
fn terms_equal(t1: Term, t2: Term) -> Bool {
  case t1, t2 {
    // Same constructors
    Ctr(name1, args1, _), Ctr(name2, args2, _) -> {
      name1 == name2 && lists_all2(terms_equal, args1, args2)
    }
    
    // Same literals
    Lit(v1, _), Lit(v2, _) -> v1 == v2
    
    // Same records (field order doesn't matter)
    Rcd(fields1, _), Rcd(fields2, _) -> {
      records_equal(fields1, fields2)
    }
    
    // Same lambdas (compare as functions)
    Lam(_, _, _), Lam(_, _, _) -> {
      // Lambdas are equal if they're alpha-equivalent
      // This is undecidable in general, so we use a conservative check
      False  // Or implement alpha-equivalence
    }
    
    // Everything else
    _, _ -> False
  }
}
```

#### Step 2: Tao Generic Operator

Expose structural equality in Tao:

```tao
// lib/prelude/equality.tao

/// Generic structural equality
///
/// Works for all types that support structural comparison
pub fn (==)<a>(x: a, y: a) -> Bool {
  %call structural_eq(x, y)
}

/// Generic structural inequality
pub fn (!=)<a>(x: a, y: a) -> Bool {
  not(x == y)
}
```

#### Step 3: Examples

```tao
// lib/prelude/equality.tao

// ============================================================================
// BUILTIN TYPES
// ============================================================================

> 42 == 42
True

> 42 != 43
True

> True == True
True

> False != True
True

// ============================================================================
// ALGEBRAIC DATA TYPES
// ============================================================================

type Point = Point(I32, I32)

> Point(1, 2) == Point(1, 2)
True

> Point(1, 2) == Point(3, 4)
False

> Point(1, 2) != Point(3, 4)
True

// ============================================================================
// NESTED TYPES
// ============================================================================

type Line = Line(Point, Point)

> Line(Point(0, 0), Point(1, 1)) == Line(Point(0, 0), Point(1, 1))
True

> Line(Point(0, 0), Point(1, 1)) == Line(Point(0, 0), Point(2, 2))
False

// ============================================================================
// RECORDS
// ============================================================================

type Person = Person { name: String, age: I32 }

> Person { name: "Alice", age: 30 } == Person { name: "Alice", age: 30 }
True

> Person { name: "Alice", age: 30 } == Person { name: "Bob", age: 30 }
False

// ============================================================================
// LISTS
// ============================================================================

type List(a) = Cons(a, List(a)) | Nil

> Cons(1, Cons(2, Nil)) == Cons(1, Cons(2, Nil))
True

> Cons(1, Cons(2, Nil)) == Cons(1, Cons(3, Nil))
False

> Nil == Nil
True

// ============================================================================
// OPTIONS
// ============================================================================

type Option(a) = Some(a) | None

> Some(42) == Some(42)
True

> Some(42) == Some(43)
False

> None == None
True

> Some(42) == None
False
```

---

### Phase 2: Trait System (Future)

#### Trait Definition

```tao
// lib/prelude/eq.tao

/// Equality trait
pub trait Eq(a) {
  /// Equality comparison
  pub fn (==)(x: a, y: a) -> Bool
  
  /// Inequality comparison (default implementation)
  pub fn (!=)(x: a, y: a) -> Bool {
    not(x == y)
  }
}
```

#### Manual Instance

```tao
// Custom equality for CaseInsensitiveString
type CaseInsensitiveString = CIS(String)

impl Eq(CaseInsensitiveString) {
  fn (==)(a: CIS, b: CIS) -> Bool {
    match (a, b) {
      | (CIS(s1), CIS(s2)) -> string_equal_ignore_case(s1, s2)
    }
  }
}
```

#### Constrained Generic Functions

```tao
// Generic function with Eq constraint
pub fn contains<a: Eq>(list: List(a), item: a) -> Bool {
  match list {
    | Nil -> False
    | Cons(x, xs) -> x == item || contains(xs, item)
  }
}

// Usage
> contains(Cons(1, Cons(2, Nil)), 2)
True

> contains(Cons(1, Cons(2, Nil)), 3)
False
```

---

## Technical Challenges

### Challenge 1: Function Equality

**Problem**: Functions can't be compared structurally:

```tao
type FnWrapper = FnWrapper(I32 -> I32)

> FnWrapper(fn(x) { x + 1 }) == FnWrapper(fn(x) { x + 1 })
// What should this return?
```

**Solution**: Don't support equality for function types:
- Compile error if trying to compare functions
- Or: Always return `False` for function comparison

---

### Challenge 2: Recursive Types

**Problem**: Infinite recursion for recursive types:

```tao
type Tree = Leaf | Node(Tree, Tree)

> let rec_tree = Node(Leaf, rec_tree) in rec_tree == rec_tree
// Infinite loop!
```

**Solution**: 
- Use step counter (like Core's evaluation)
- Limit comparison depth
- Detect cycles via pointer equality (if available)

---

### Challenge 3: Type Parameters

**Problem**: Generic types need element equality:

```tao
type List(a) = Cons(a, List(a)) | Nil

// How to compare List(a) without knowing if 'a' supports equality?
```

**Solution**: 
- Phase 1: Structural equality works for all types (no constraints)
- Phase 2: Add `Eq(a)` constraint for generic types

---

## Examples by Type Category

### Primitive Types

```tao
// Integers
> 42 == 42
True

> 42 == 43
False

// Floats
> 3.14 == 3.14
True

> 3.14 == 3.15
False

// Booleans
> True == True
True

> True == False
False
```

### Product Types (Tuples/Records)

```tao
// Tuples
> (1, 2) == (1, 2)
True

> (1, 2) == (3, 4)
False

// Records
type Point = Point { x: I32, y: I32 }

> Point { x: 1, y: 2 } == Point { x: 1, y: 2 }
True

> Point { x: 1, y: 2 } == Point { x: 3, y: 4 }
False

// Field order shouldn't matter
> Point { x: 1, y: 2 } == Point { y: 2, x: 1 }
True
```

### Sum Types (Variants)

```tao
type Option(a) = Some(a) | None

> Some(42) == Some(42)
True

> Some(42) == None
False

> None == None
True

type Result(a, e) = Ok(a) | Err(e)

> Ok(42) == Ok(42)
True

> Ok(42) == Ok(43)
False

> Err("error") == Err("error")
True

> Ok(42) == Err("error")
False
```

### Recursive Types

```tao
type List(a) = Cons(a, List(a)) | Nil

> Cons(1, Cons(2, Nil)) == Cons(1, Cons(2, Nil))
True

> Cons(1, Nil) == Cons(2, Nil)
False

> Nil == Nil
True

type Tree = Leaf | Node(I32, Tree, Tree)

> Node(1, Leaf, Leaf) == Node(1, Leaf, Leaf)
True

> Node(1, Leaf, Leaf) == Node(2, Leaf, Leaf)
False
```

---

## Implementation Checklist

### Phase 1: Core Structural Equality

- [ ] Add `structural_eq` FFI builtin to Core
- [ ] Implement `terms_equal` for normalized comparison
- [ ] Handle all term types (Ctr, Lit, Rcd, etc.)
- [ ] Add step counter to prevent infinite loops
- [ ] Test with simple ADTs
- [ ] Test with nested types
- [ ] Test with recursive types
- [ ] Document limitations (functions, etc.)

### Phase 2: Tao Generic Operator

- [ ] Define generic `==` operator in Tao
- [ ] Add examples for all type categories
- [ ] Add REPL-style tests
- [ ] Document behavior and limitations

### Phase 3: Trait System (Future)

- [ ] Design trait syntax
- [ ] Implement trait resolution
- [ ] Add `Eq` trait
- [ ] Support constrained generics
- [ ] Allow manual instances

---

## Success Criteria

Phase 1 is complete when:

1. ✅ `structural_eq` FFI builtin works in Core
2. ✅ Generic `==` operator works for all ADTs
3. ✅ Examples produce expected output
4. ✅ No infinite loops on recursive types
5. ✅ Clear error messages for unsupported types

---

## Related Documents

- **[../core/03-ffi-comptime.md](../core/03-ffi-comptime.md)** - Core FFI builtins
- **[../tao/10-overloading-design.md](../tao/10-overloading-design.md)** - Operator overloading
- **[../core/core.gleam](../../src/core/core.gleam)** - Core language implementation

---

## Change Log

| Date | Change |
|------|--------|
| March 2026 | Initial generic equality plan created |
