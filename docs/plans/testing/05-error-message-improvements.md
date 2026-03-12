# Error Message Improvements

> **Goal**: Improve error message quality to match Rust/compiler standards
> **Status**: 📋 Planned
> **Date**: March 11, 2026

---

## Overview

Current error messages are functional but can be significantly improved. This plan outlines incremental improvements to make error messages more helpful, actionable, and user-friendly.

---

## Current State

### What Works
- ✅ Error codes (E0001, E0101, etc.)
- ✅ Source snippets with line numbers
- ✅ Basic hints
- ✅ Emoji formatting (❌, 💡, 📝, 🔧)
- ✅ Multiple error accumulation

### What Needs Improvement
- [ ] Context lines (currently shows minimal context)
- [ ] "Did you mean?" suggestions
- [ ] Type information in messages
- [ ] Better explanations of _why_ something is wrong
- [ ] Cross-file error reporting
- [ ] Error chaining for cascading errors

---

## Improvement Phases

### Phase 1: Context Lines (Low Effort, High Impact)

**Goal**: Show 2-3 lines of context before and after errors.

**Current**:
```
   ┌─ file:3:5
   │
 3 │ x + 1
   │     ^
   │
```

**Target**:
```
   ┌─ file:3:5
   │
 1 │ let x = 1
 2 │ let y = 2
 3 │ x + 1
   │     ^ expected Int, found String
 4 │ let z = y + x
 5 │ in z
   │
```

**Implementation**:
```gleam
// In source_snippet.gleam
let context_lines = 2
let start_line = max(1, error_line - context_lines)
let end_line = min(total_lines, error_line + context_lines)
```

**Effort**: ~1 hour
**Impact**: High - users can understand context without scrolling

---

### Phase 2: "Did You Mean?" Suggestions

**Goal**: Suggest fixes for common errors.

#### Type Mismatches

**Current**:
```
error[E0101]: Type mismatch
  = note: Int and $Type are incompatible types
  = hint: Check that the expression has the expected type
```

**Target**:
```
error[E0101]: Type mismatch
  = note: Int and $Type are incompatible types
  💡 The value 1 is of type Int
  💡 The type annotation expects a value of type $Type
  🔧 help: Did you mean? `1 : Int`
  🔧 help: Or use a different type annotation
```

#### Undefined Variables

**Current**:
```
error[E0102]: Undefined variable
  = hint: Check variable name and scope
```

**Target**:
```
error[E0102]: Undefined variable
  ┌─ file:3:5
  │
3 │ rec(x)
  │     ^
  │
  = note: Variable `x` is not defined
  💡 A variable with a similar name exists: `rec`
  🔧 help: Did you mean to use `rec`?
  🔧 help: Or define `x` before using it
```

**Implementation**:
```gleam
// Find similar names using Levenshtein distance
fn find_similar(name: String, scope: Scope) -> List(String) {
  scope.variables
  |> list.filter(fn(v) { levenshtein(name, v) <= 2 })
}
```

**Effort**: ~4 hours
**Impact**: High - helps users fix errors faster

---

### Phase 3: Better Type Information

**Goal**: Show full type information in error messages.

#### Current Limitations
- Type names are abbreviated
- Function types not shown clearly
- Generic types not instantiated

**Target**:
```
error[E0101]: Type mismatch
   ┌─ file:5:10
   │
 5 │ f(x)
   │   ^
   │
   = note: Argument type mismatch
   = expected: fn(Int) -> String
   = got:      Int
   │
   💡 The function `f` expects an argument of type Int
   💡 You are passing a value of type String
   🔧 help: Convert the String to Int, or change the function signature
```

**Effort**: ~8 hours
**Impact**: Medium - helps understand complex type errors

---

### Phase 4: Error Explanations

**Goal**: Explain _why_ something is wrong, not just _what_ is wrong.

#### Example: Type Mismatch

**Current**:
```
error[E0101]: Type mismatch
  = note: Int and $Type are incompatible types
```

**Target**:
```
error[E0101]: Type mismatch
   ┌─ file:2:5
   │
 2 │ 1 : $Type
   │     ^^^^^
   │
   = note: Int and $Type are incompatible types
   │
   = explanation: 
     In this language, `$Type` is the type of types (a universe).
     The value `1` is an integer literal with type `Int`.
     You cannot annotate a value with a universe - universes are for types.
   │
   💡 Use `Int` for integer values
   💡 Use `$Type` when working with types themselves
   🔧 help: Change `$Type` to `Int`
```

**Effort**: ~16 hours (requires writing explanations for all error types)
**Impact**: High - helps users learn the language

---

### Phase 5: Error Chaining

**Goal**: Show how errors cascade from a single root cause.

**Current**: All errors shown equally
```
error[E0102]: Undefined variable `x`
error[E0103]: Not a function
error[E0101]: Type mismatch
```

**Target**: Root cause highlighted
```
error[E0102]: Undefined variable `x` (root cause)
   ┌─ file:3:5
   │
 3 │ x + 1
   │ ^
   │
   = note: `x` is not defined
   💡 This error causes 2 additional errors below
   🔧 help: Define `x` to fix this and subsequent errors

error[E0103]: Not a function (caused by above)
   ┌─ file:4:10
   │
 4 │ f(x)(y)
   │          ^
   │
   = note: Cannot call undefined variable

error[E0101]: Type mismatch (caused by above)
   ┌─ file:5:5
   │
   │
```

**Effort**: ~20 hours (requires error dependency tracking)
**Impact**: Medium - helps prioritize fixes

---

## Priority Order

| Phase | Effort | Impact | Priority |
|-------|--------|--------|----------|
| 1. Context Lines | ~1h | High | 1st |
| 2. "Did You Mean?" | ~4h | High | 2nd |
| 3. Type Information | ~8h | Medium | 3rd |
| 4. Error Explanations | ~16h | High | 4th |
| 5. Error Chaining | ~20h | Medium | 5th |

---

## Implementation Notes

### Testing Changes

After each improvement:
1. Update golden files: `./scripts/generate_golden_files.sh`
2. Review diff: `git diff examples/core/`
3. Run tests: `gleam test`
4. Verify error messages are clearer

### Measuring Success

Track:
- Time to fix errors (user feedback)
- Number of repeated errors (are users learning?)
- GitHub issues about confusing errors

### Avoiding Over-Engineering

**Do**:
- ✅ Start with simple improvements (context lines)
- ✅ Test with real users
- ✅ Iterate based on feedback

**Don't**:
- ❌ Build complex ML-based suggestions initially
- ❌ Write novel-length explanations
- ❌ Show too much information (cognitive load)

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Testing overview
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing spec
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - CLI commands spec
- **[../error-reporting/02-error-types.md](../error-reporting/02-error-types.md)** - Error types

---

## References

- [Rust Compiler Errors](https://github.com/rust-lang/rust/blob/master/compiler/rustc_errors/src)
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans)
- [Error Formatter](../../src/core/error_formatter.gleam)
- [Source Snippet](../../src/syntax/source_snippet.gleam)
