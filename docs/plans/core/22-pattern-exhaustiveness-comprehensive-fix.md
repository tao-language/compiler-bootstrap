# Pattern Exhaustiveness Bug - Comprehensive Fix Plan

> **Date**: March 2026
> **Status**: 🐛 Root Cause Identified (Grammar Backtracking Limitation)
> **Test Status**: 520/522 tests passing (99.6%)

---

## Executive Summary

**Root Cause**: The grammar library's `alt()` function doesn't support backtracking based on action function return values. Once a pattern matches, the alternative is considered successful, even if the action returns an error value like `Int(0)`.

**Problem**: In `PrimaryPattern`, the constructor alternative uses `token_pattern("Ident")`, which matches both uppercase and lowercase identifiers. When it matches a lowercase identifier (like `n`), it returns `Int(0)` (error value), but the `alt()` doesn't try the next alternative (variable pattern).

**Current Workaround**: The constructor alternative checks `is_uppercase_start()` and returns `Int(0)` for lowercase identifiers. But this doesn't work because the `alt()` has already matched.

---

## Solution Options

### Option 1: Lexer Token Distinction (Recommended)

**Approach**: Modify the lexer to produce different tokens for uppercase (`UIdent`) and lowercase (`LIdent`) identifiers.

**Pros**:
- Clean separation of concerns
- Grammar can use appropriate token patterns
- No backtracking needed

**Cons**:
- Requires updating all uses of `Ident` in the grammar
- Big change, but systematic

**Implementation**:
1. Update lexer to produce `UIdent` for uppercase, `LIdent` for lowercase
2. Update grammar:
   - `PrimaryPattern`: Use `UIdent` for constructors, `LIdent` for variables
   - Other rules: Use `LIdent` for variable names, `UIdent` for type names
3. Test all pattern types

### Option 2: Grammar Restructuring

**Approach**: Restructure the grammar to avoid the backtracking issue.

**Pros**:
- No lexer changes needed

**Cons**:
- Complex grammar logic
- Harder to maintain

**Implementation**:
- Merge constructor and variable alternatives into a single alternative
- Handle uppercase/lowercase distinction in the action function
- Return appropriate expression based on case

### Option 3: Grammar Library Enhancement

**Approach**: Add support for conditional matching or backtracking in the grammar library.

**Pros**:
- Clean solution for this and future issues

**Cons**:
- Requires changes to the grammar library
- More complex grammar library

**Implementation**:
- Add `guard` parameter to `alt()` or `seq()`
- Or add `satisfy` pattern that checks a predicate

---

## Recommended Approach: Option 1

Option 1 is the cleanest and most maintainable solution. It separates the lexical analysis (identifying uppercase vs lowercase) from the grammar logic.

### Implementation Plan

#### Step 1: Update Lexer

Modify `get_ident_kind()` in `src/syntax/lexer.gleam`:

```gleam
fn get_ident_kind(value: String) -> String {
  let keyword_kind = get_keyword_kind(value)
  case keyword_kind != "Ident" {
    True -> keyword_kind
    False -> {
      case string.is_empty(value) {
        True -> "Ident"
        False -> {
          let first = string.slice(value, 0, 1)
          case first {
            "A" | "B" | ... | "Z" -> "UIdent"
            _ -> "LIdent"
          }
        }
      }
    }
  }
}
```

#### Step 2: Update Pattern Grammar

Update `PrimaryPattern` in `src/tao/syntax.gleam`:

```gleam
rule("PrimaryPattern", [
  // Wildcard
  alt(token_pattern("Underscore"), ...),
  
  // Constructor (uppercase only)
  alt(
    seq([token_pattern("UIdent"), opt(...)]),
    fn(values) { ... Ctr(...) }
  ),
  
  // Variable (lowercase only)
  alt(
    token_pattern("LIdent"),
    fn(values) { ... Var(...) }
  ),
  
  // Literal
  alt(token_pattern("Number"), ...),
  
  // ... other patterns
])
```

#### Step 3: Update Other Grammar Rules

Update all uses of `Ident` in the grammar:
- Variable names (let bindings, function params, etc.): Use `LIdent`
- Type names, constructor names: Use `UIdent`
- Module names: Use `Ident` (can be either)

#### Step 4: Test

Test all pattern types:
- Wildcard: `match x { | _ -> 100 }`
- Variable: `match x { | n -> 100 }`
- Literal: `match x { | 0 -> 100 }`
- Constructor: `match opt { | Some(x) -> x | None -> 0 }`
- Record, Tuple, List, Or, As patterns

---

## Current Status

- ✅ Lexer updated to produce `UIdent` and `LIdent`
- ✅ Pattern grammar updated to use `UIdent` and `LIdent`
- ❌ Other grammar rules still use `Ident` (causing parse errors)
- ❌ Tests failing due to parse errors

## Next Steps

1. Systematically update all uses of `Ident` in the grammar
2. Test each rule individually
3. Run full test suite
4. Verify all pattern types work correctly
5. Verify exhaustiveness checking works for wildcards and variables

---

## Lessons Learned

1. **Grammar Library Limitations**: The `alt()` function doesn't support backtracking based on action return values. This is a fundamental limitation that affects grammar design.

2. **Lexer-Grammar Contract**: The lexer and grammar must agree on token kinds. If the grammar expects different tokens for different identifier types, the lexer must produce them.

3. **Early Testing**: This issue could have been caught earlier with comprehensive pattern parsing tests.

4. **Incremental Changes**: Big changes (like updating all `Ident` uses) should be done incrementally with testing at each step.

---

## Related Documents

- **[docs/plans/core/21-wildcard-pattern-fix-summary.md](./21-wildcard-pattern-fix-summary.md)** - Previous fix summary
- **[src/syntax/lexer.gleam](../../src/syntax/lexer.gleam)** - Lexer implementation
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Grammar implementation
