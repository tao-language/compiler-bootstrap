# Constructor Environment for Exhaustiveness Checking - Implementation Status

> **Date**: March 2026
> **Status**: ✅ Core Infrastructure Complete, ⏳ Grammar Parsing Needs Refinement
> **Goal**: Populate State.ctrs from Tao type definitions for constructor pattern exhaustiveness

---

## Architecture Principle

**State should NOT have hardcoded constructor definitions.** Constructor definitions should be derived from Tao's type definitions in the source code.

---

## Current Status

### ✅ Completed

1. **Type Definition AST** - Added `StmtType`, `Constructor`, `ConstructorField`, `TypeAst` to `src/tao/ast.gleam`
2. **Desugar Context** - Added `ctrs` field to `DesugarContext`
3. **Type Processing** - Added `process_type_definitions()` to populate constructor environment
4. **Integration** - Pass `ctrs` from desugaring to type checking in `compiler_bootstrap.gleam`
5. **Exhaustiveness** - Updated `get_type_family()` to use custom constructor definitions

### ⏳ Known Issues

1. **Grammar Parsing for Constructor Fields** - Gleam's pattern matching limitations with nested case expressions cause type inference issues. The grammar rule for `Constructor` needs refinement.

2. **Type Parameters Not Supported** - Only simple types work (e.g., `type Option = Some(Int) | None`). Type parameters like `type Option(a)` are not yet supported.

3. **Named Constructor Fields Not Supported** - Only unnamed fields work (e.g., `Some(Int)`). Named fields like `Cons { head: Int, tail: List }` need additional work.

---

## Implementation Learnings

### Learning 1: Grammar Rule Return Types Must Match

The grammar rule for `Type` returns `Stmt`, but nested rules like `Constructor` return `Constructor`. When using `ref("Constructor")` inside the `Type` rule, the values are wrapped in `AstValue(Constructor)`, not returned directly.

**Solution**: Extract the inner value using pattern matching on `AstValue`.

### Learning 2: Gleam Case Pattern Matching Limitations

Gleam doesn't support complex nested pattern matching in case expressions when dealing with grammar values. The `Value` type wrapper causes type inference issues.

**Workaround**: Use helper functions that extract values step by step, avoiding nested case expressions.

### Learning 3: List Value Structure from Grammar

The `many()` combinator returns `ListValue(List([TokenValue, TokenValue]))`, not a plain list. Each element is wrapped in `Value`.

**Solution**: Unwrap `ListValue` before processing, use helper functions to extract token values.

### Learning 4: AstValue Wrapping

When a rule returns a value through `alt()`, it's wrapped in `AstValue`. This means:

```gleam
// Constructor rule returns: AstValue(Constructor)
// But Type rule expects: Constructor directly
```

**Solution**: Unwrap `AstValue` in the parent rule's action function.

### Learning 5: Type Inference with Polymorphic Grammar

The grammar is `Grammar(Expr)`, but rules can return different types (Stmt, Constructor, etc.). Type inference can get confused when action functions return different types than expected.

**Workaround**: Keep action functions simple, use helper functions for complex transformations.

---

## Technical Details

### Type Definition Syntax (Current)

```tao
// Simple type without parameters
type Option = Some(Int) | None

// Constructor with unnamed fields
type Result = Ok(Int) | Err(String)

// Nullary constructor
type Bool = True | False
```

### Type Definition Syntax (Future)

```tao
// With type parameters (not yet supported)
type Option(a) = Some(a) | None

// With named fields (not yet supported)
type List(a) = Cons { head: a, tail: List(a) } | Nil
```

### Core CtrDef Structure

```gleam
CtrDef(
  params: List(String),      // Type parameters: ["a", "e"]
  arg_ty: Term,              // Argument type (fields)
  ret_ty: Term,              // Return type (type application)
)
```

---

## Files Modified

| File | Changes |
|------|---------|
| `src/tao/ast.gleam` | Added `StmtType`, `Constructor`, `ConstructorField`, `TypeAst` |
| `src/tao/desugar.gleam` | Added `ctrs` field, `process_type_definitions()` |
| `src/compiler_bootstrap.gleam` | Added `update_state_ctrs()` |
| `src/core/core.gleam` | Updated `get_type_family()` to use custom constructors |

### Files Needing Work

| File | Issue |
|------|-------|
| `src/tao/syntax.gleam` | Constructor grammar rule needs refinement for proper type inference |

---

## Next Steps

### Immediate (Fix Grammar Parsing)

1. **Simplify Constructor rule** - Use a simpler grammar structure that avoids nested pattern matching
2. **Test incrementally** - Build after each small change
3. **Consider alternative approaches** - Maybe parse constructors differently

### Short Term (Add Features)

1. **Add type parameter support** - Parse `(a, b)` in `type Name(a, b) = ...`
2. **Add named field support** - Parse `{ field: Type }` syntax
3. **Improve error messages** - Better diagnostics for type definition errors

### Long Term (Complete Feature)

1. **Test exhaustiveness checking** - Verify constructor patterns are checked correctly
2. **Add prelude types** - Write Option, Result, etc. in Tao
3. **Auto-import prelude** - Make prelude types available by default

---

## Testing Strategy

### Unit Tests

1. Parse simple type: `type Bool = True | False`
2. Parse type with fields: `type Option = Some(Int) | None`
3. Parse nullary constructor: `None`
4. Parse unary constructor: `Some(Int)`

### Integration Tests

1. Type check match with exhaustive patterns
2. Type check match with missing patterns (should error)
3. Type check match with wildcard (should be exhaustive)

### Example Programs

```tao
// test_exhaustive.tao
type Option = Some(Int) | None

let x = Some(42)
match x {
  | Some(v) -> v
  | None -> 0  // Exhaustive - no error
}
```

```tao
// test_missing.tao
type Option = Some(Int) | None

let x = Some(42)
match x {
  | Some(v) -> v  // Missing None - should error
}
```

---

## Related Documents

- **[docs/plans/core/24-constructor-environment-plan.md](./24-constructor-environment-plan.md)** - This document
- **[docs/plans/core/25-pattern-exhaustiveness-status.md](./25-pattern-exhaustiveness-status.md)** - Previous status
- **[docs/plans/core/23-pattern-exhaustiveness-final-fix.md](./23-pattern-exhaustiveness-final-fix.md)** - Wildcard/variable fix
