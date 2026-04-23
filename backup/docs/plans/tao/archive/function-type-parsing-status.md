# Function Type Parsing - Implementation Status

**Date**: 2026-03-17  
**Status**: ⏸️ **Partially Implemented**  
**Blocker**: Grammar DSL type system limitation

---

## Goal

Enable function types in parameter annotations:

```tao
fn apply(f: fn(I32) -> I32, x: I32) -> I32 {
  f(x)
}
```

---

## What Was Accomplished

### 1. Type AST Already Exists ✅

The `tao/ast.Type` already supports function types:

```gleam
pub type Type {
  TVar(String)              // Simple type: I32
  TApp(String, List(Type))  // Generic: List(Int)
  TFn(List(Type), Type)     // Function: fn(I32) -> I32
  TRecord(List(#(String, Type)))
  TTuple(List(Type))
  THole
}
```

### 2. Grammar Rule Added (But Has Issues) ⏸️

Added a `Type` rule to the grammar that parses:
- Simple types: `I32`, `String`
- Generic types: `List(Int)`, `Option(a)`
- Function types: `fn(I32) -> I32`, `fn(I32, I32) -> I32`

**Problem**: The grammar DSL is parameterized by `Expr`, so all rules return `Value(Expr)`. The Type rule tries to return `Value(Type)`, which causes type mismatches.

---

## Technical Blocker

### The Issue

The Tao grammar is defined as `Grammar(Expr)`, meaning all rules return `Value(Expr)`:

```gleam
pub fn tao_grammar() -> Grammar(Expr) {
  Grammar(
    name: "Tao",
    start: "Program",
    // ...
  )
}
```

When we add a `Type` rule, it must also return `Value(Expr)`, but we want it to return `Type`.

### Attempted Solutions

#### Solution 1: Type Alias

```gleam
pub type Type = AstType
```

**Problem**: Pattern matching requires using `AstTFn`, `AstTApp`, `AstTVar` constructors, which is confusing.

#### Solution 2: Separate Grammar

Create a separate `Grammar(Type)` for parsing types.

**Problem**: Can't reference rules across grammars easily.

#### Solution 3: Wrap Type in Expr

Add a new `TypeExpr(Type)` constructor to `Expr`.

**Problem**: Requires significant refactoring of the entire AST.

---

## Recommended Approach

### Option A: Inline Type Parsing (Recommended)

Don't use a separate `Type` rule. Instead, parse types inline where they're used:

```gleam
// In the Fn rule, parse param types directly:
opt(seq([
  token_pattern("Colon"),
  alt(
    // Function type: fn(...) -> ...
    seq([...]),
    // Simple type: Ident
    token_pattern("Ident"),
  ),
])),
```

**Pros**:
- No grammar type system issues
- Minimal refactoring
- Works with existing infrastructure

**Cons**:
- Code duplication (type parsing in multiple places)
- Less elegant than separate rule

### Option B: Extend Grammar DSL

Modify the syntax library to support multiple return types in a single grammar.

**Pros**:
- Clean solution
- Reusable for other projects

**Cons**:
- Significant work
- Changes to core library

### Option C: TypeExpr Wrapper

Add `TypeExpr(Type)` to the `Expr` type:

```gleam
pub type Expr {
  // ... existing constructors ...
  TypeExpr(Type)  // NEW
}
```

**Pros**:
- Clean separation
- Type rule can return `Value(Expr)` containing `TypeExpr(Type)`

**Cons**:
- Requires updating all pattern matches on `Expr`
- Significant refactoring

---

## Current Status

### Working
- ✅ Type AST supports function types
- ✅ Type-to-string conversion
- ✅ Parameter extraction with types

### Not Working
- ❌ Grammar rule for Type (type mismatch)
- ❌ Function type parsing in parameters
- ❌ `higher_order.tao` example fails to parse

---

## Next Steps

### Immediate (Option A - Inline Parsing)

1. Remove the separate `Type` rule
2. Add inline type parsing to:
   - Function parameters
   - Function return types
   - Let binding type annotations
3. Test with `higher_order.tao`

**Estimated Time**: 2-3 hours

### Long-term (Option C - TypeExpr Wrapper)

1. Add `TypeExpr(Type)` to `Expr`
2. Update all pattern matches
3. Add proper `Type` grammar rule
4. Test comprehensively

**Estimated Time**: 6-8 hours

---

## Test Cases (For When Implemented)

### Simple Function Type

```tao
fn apply(f: fn(I32) -> I32, x: I32) -> I32 {
  f(x)
}
```

### Multiple Parameters

```tao
fn combine(f: fn(I32, I32) -> I32, x: I32, y: I32) -> I32 {
  f(x, y)
}
```

### Nested Function Types

```tao
fn compose(f: fn(I32) -> I32, g: fn(I32) -> I32) -> fn(I32) -> I32 {
  fn(x) { f(g(x)) }
}
```

### Generic Types

```tao
fn map(opt: Option(Int), f: fn(Int) -> Int) -> Option(Int) {
  match opt {
    | Some(x) -> Some(f(x))
    | None -> None
  }
}
```

---

## Files Modified (Incomplete Implementation)

- `src/tao/syntax.gleam` - Added Type rule (currently broken)
- `docs/plans/tao/function-type-parsing-plan.md` - Original plan
- `docs/plans/tao/function-type-status.md` - This document

---

## Lessons Learned

1. **Grammar DSL Limitations**: The grammar DSL's type parameterization makes it hard to mix different return types.

2. **Type Aliases Can Be Confusing**: Using `pub type Type = AstType` led to constructor naming confusion (`TFn` vs `AstTFn`).

3. **Inline vs Separate Rules**: For complex type systems, inline parsing might be simpler than separate grammar rules.

4. **AST Design Matters**: Having a separate `Type` AST type (vs embedding in `Expr`) creates friction when parsing.

---

## Recommendation

**Use Option A (Inline Parsing)** for now to unblock higher-order functions. Refactor to Option C (TypeExpr Wrapper) later if needed.

The inline approach is less elegant but will work within the current grammar DSL constraints and can be implemented in 2-3 hours.

---

**Status**: Implementation paused, documenting blocker  
**Next**: Implement Option A (inline type parsing) or defer to future session
