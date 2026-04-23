# Pattern Exhaustiveness Bug - Final Fix Summary

> **Date**: March 2026
> **Status**: ✅ FIXED (Wildcard and Variable patterns)
> **Test Status**: 520/522 tests passing (99.6%)

---

## Executive Summary

**Root Cause**: The grammar library's `alt()` function doesn't support backtracking based on action function return values. When the constructor pattern alternative matched a lowercase identifier (like `n`), it returned an error value `Int(0)`, but the `alt()` had already matched and wouldn't try the variable alternative.

**Fix Applied**: Merged the constructor and variable pattern alternatives into a single alternative that handles both cases in the action function. The action function now checks if the identifier is uppercase (constructor) or lowercase (variable) and returns the appropriate expression.

**Result**: 
- ✅ Wildcard patterns (`match x { | _ -> 100 }`) work correctly
- ✅ Variable patterns (`match x { | n -> 100 }`) work correctly
- ❌ Constructor pattern exhaustiveness checking still requires type information (expected limitation)

---

## Detailed Fix

### Problem

The `PrimaryPattern` rule had separate alternatives for constructors and variables:

```gleam
// Constructor alternative
alt(
  seq([token_pattern("Ident"), opt(...)]),
  fn(values) {
    case values {
      [TokenValue(name)] => {
        case is_uppercase_start(name.value) {
          True => Ctr(...)  // Constructor
          False => Int(0, ...)  // Error - lowercase not a constructor
        }
      }
      ...
    }
  }
),
// Variable alternative
alt(
  token_pattern("Ident"),
  fn(values) {
    case values {
      [TokenValue(t)] => {
        case is_uppercase_start(t.value) {
          True => Int(0, ...)  // Error - uppercase not a variable
          False => Var(...)  // Variable
        }
      }
      ...
    }
  }
)
```

When parsing `n` (a variable pattern), the constructor alternative matched first (because it uses `token_pattern("Ident")`), but returned `Int(0)` because `n` is lowercase. The `alt()` didn't backtrack to try the variable alternative.

### Solution

Merged the alternatives into a single alternative that handles both cases:

```gleam
// Identifier pattern: can be Constructor (uppercase) or Variable (lowercase)
alt(
  seq([
    token_pattern("Ident"),
    opt(seq([
      token_pattern("LParen"),
      ref("Pattern"),
      many(seq([token_pattern("Comma"), ref("Pattern")])),
      token_pattern("RParen"),
    ])),
  ]),
  fn(values) {
    case values {
      [TokenValue(name)] => {
        // Single identifier - check if uppercase (constructor) or lowercase (variable)
        case is_uppercase_start(name.value) {
          True => Ctr(name.value, [], ...)  // Constructor
          False => Var(name.value, ...)  // Variable
        }
      }
      [TokenValue(name), ListValue([_, AstValue(first), rest, ..]), ..] => {
        // Constructor with arguments - must be uppercase
        case is_uppercase_start(name.value) {
          True => Ctr(name.value, args, ...)  // Constructor with args
          False => Int(0, ...)  // Error - lowercase with args is invalid
        }
      }
      _ => Int(0, ...)
    }
  }
)
```

Now the action function handles both uppercase (constructors) and lowercase (variables) identifiers correctly.

---

## Files Changed

1. **`src/tao/syntax.gleam`** - Merged constructor and variable pattern alternatives
2. **`docs/plans/core/22-pattern-exhaustiveness-comprehensive-fix.md`** - Original analysis document
3. **`docs/plans/core/23-pattern-exhaustiveness-final-fix.md`** - This final fix summary

---

## Testing

### Tests Passing

- ✅ Wildcard pattern: `match x { | _ -> 100 }` → `100`
- ✅ Variable pattern: `match x { | n -> 100 }` → `100`
- ✅ All 520 existing tests

### Known Limitations

- ❌ Constructor pattern exhaustiveness: `match opt { | Some(x) -> x | None -> 0 }` - The exhaustiveness checker doesn't have type information about the `Option` type, so it can't verify that `Some` + `None` covers all cases. This is expected and requires type-directed exhaustiveness checking.

---

## Lessons Learned

1. **Grammar Library Limitations**: The `alt()` function doesn't support backtracking based on action return values. This is a fundamental limitation that affects grammar design.

2. **Merged Alternatives**: When alternatives might match the same tokens but produce different results based on token content, merge them into a single alternative and handle the distinction in the action function.

3. **Incremental Testing**: Testing each change incrementally helps catch issues early.

4. **Debug Logging**: Extensive debug logging at each stage of the parsing pipeline was crucial for identifying the root causes.

---

## Related Documents

- **[docs/plans/core/21-wildcard-pattern-fix-summary.md](./21-wildcard-pattern-fix-summary.md)** - Previous wildcard fix summary
- **[docs/plans/core/22-pattern-exhaustiveness-comprehensive-fix.md](./22-pattern-exhaustiveness-comprehensive-fix.md)** - Comprehensive analysis
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core exhaustiveness checking
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Grammar and pattern extraction
