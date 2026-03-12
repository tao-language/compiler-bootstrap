# Error Message Improvements

> **Goal**: Improve error message quality to match Rust/compiler standards
> **Status**: ⏳ In Progress - Phase 1-3 complete
> **Date**: March 11, 2026

---

## Overview

Current error messages are functional but can be significantly improved. This plan outlines incremental improvements to make error messages more helpful, actionable, and user-friendly.

---

## Current State

### What Works (as of March 2026)
- ✅ Error codes (E0101, E0102, etc.)
- ✅ Source snippets with line numbers
- ✅ **3 lines of context** before and after errors (Phase 1)
- ✅ Multiple hints per error
- ✅ Type information in error messages (Phase 3)
- ✅ Emoji formatting (❌, 💡, 📝, 🔧)
- ✅ Multiple error accumulation
- ✅ **376 tests passing**

### What Needs Improvement
- [ ] "Did you mean?" suggestions with Levenshtein distance (blocked by De Bruijn indices)
- [ ] Better type information (full type pretty-printing)
- [ ] Error explanations (_why_ something is wrong)
- [ ] Cross-file error reporting
- [ ] Error chaining for cascading errors

---

## Improvement Phases

### Phase 1: Context Lines ✅ COMPLETE

**Goal**: Show 3 lines of context before and after errors.

**Status**: ✅ Implemented in `src/syntax/source_snippet.gleam`

**Implementation**:
```gleam
// In source_snippet.gleam
let context_lines = 3  // Changed from 2
let min_line = int.max(0, primary.start_line - context_lines - 1)
let max_line = int.min(list.length(lines), primary.end_line + context_lines)
```

**Effort**: ~30 minutes
**Impact**: High - users can understand context without scrolling

### Phase 2: Enhanced Hints ✅ COMPLETE

**Goal**: Provide multiple helpful hints for each error type.

**Status**: ✅ Implemented in `src/syntax/error_reporter.gleam`

**Implementation**:
```gleam
// VarUndefined now has multiple hints
hints: [
  "Check variable name and scope",
  "Did you forget to define this variable?"
]

// HoleUnsolved has educational hints
hints: [
  "Holes are placeholders that must be filled",
  "Provide a term of the expected type, or add a type annotation"
]

// NotAFunction has actionable hints
hints: [
  "Only functions can be called with parentheses",
  "Check that you're calling a function, not a value"
]
```

**Effort**: ~1 hour
**Impact**: High - helps users understand how to fix errors

### Phase 3: Type Information ✅ COMPLETE

**Goal**: Show full type information in error messages.

**Status**: ✅ Implemented in `src/syntax/error_reporter.gleam`

**Implementation**:
```gleam
// TypeMismatch now shows actual types
notes: [expected_str <> " and " <> got_str <> " are incompatible types"]

// value_to_string() converts types to readable format
fn value_to_string(value) -> String {
  case value {
    core.VTyp(universe) -> "$Type(" <> int.to_string(universe) <> ")"
    core.VLit(literal) -> literal_to_string(literal)
    core.VLitT(literal_type) -> literal_type_to_string(literal_type)
    core.VNeut(head, _spine) -> head_to_string(head)
    core.VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    core.VLam(name, _env, _body) -> "fn(" <> name <> ") { ... }"
    // ... etc
  }
}
```

**Supported Types**:
- `$Type(n)` - Universe types
- `Int`, `Int64`, `UInt32`, `UInt64` - Integer types
- `Float`, `Float32` - Floating point types
- `#Tag(arg)` - Constructors
- `fn(x) { ... }` - Functions
- `{field: Type}` - Records

**Effort**: ~2 hours
**Impact**: High - users can see exactly what types are incompatible

### Phase 4: "Did You Mean?" Suggestions 📋 PLANNED

**Goal**: Suggest similar variable names for undefined variables.

**Status**: 📋 Planned (blocked by De Bruijn indices)

**Challenge**: The core language uses De Bruijn indices, so variable names aren't available in the type checker. Names only exist in the syntax (Term), not in the semantics (Value/Context).

**Possible Solutions**:
1. Track names separately in the type checker state
2. Map De Bruijn indices back to names using the syntax tree
3. Provide generic suggestions based on common patterns

**Effort**: ~4 hours (requires core language changes)
**Impact**: Medium - helpful but not critical

### Phase 5: Error Explanations 📋 PLANNED

**Goal**: Explain _why_ something is wrong, not just _what_ is wrong.

**Status**: 📋 Planned

**Example**:
```
error[E0101]: Type mismatch
   ┌─ file:2:5
   │
 2 │ 1 : $Type
   │     ^^^^^
   │
   = explanation: 
     In this language, `$Type` is the type of types (a universe).
     The value `1` is an integer literal with type `Int`.
     You cannot annotate a value with a universe - universes are for types.
   │
   💡 Use `Int` for integer values
   💡 Use `$Type` when working with types themselves
```

**Effort**: ~8 hours (requires writing explanations for all error types)
**Impact**: High - helps users learn the language

---

## Priority Order

| Phase | Effort | Impact | Priority | Status |
|-------|--------|--------|----------|--------|
| 1. Context Lines | ~30 min | High | 1st | ✅ Complete |
| 2. Enhanced Hints | ~1h | High | 2nd | ✅ Complete |
| 3. Type Information | ~2h | High | 3rd | ✅ Complete |
| 4. "Did You Mean?" | ~4h | Medium | 4th | 📋 Planned |
| 5. Error Explanations | ~8h | High | 5th | 📋 Planned |

---

## Testing Changes

After each improvement:
1. Update golden files: `./scripts/generate_golden_files.sh`
2. Review diff: `git diff examples/core/`
3. Run tests: `gleam test`
4. Verify error messages are clearer

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Testing overview
- **[03-examples-testing.md](./03-examples-testing.md)** - Examples testing spec
- **[04-cli-golden-files.md](./04-cli-golden-files.md)** - Golden file format
- **[../cli/04-check-run-commands.md](../cli/04-check-run-commands.md)** - CLI commands spec
- **[../cli/03-error-reporter.md](../cli/03-error-reporter.md)** - Error reporter spec

---

## References

- [Error Reporter Implementation](../../src/syntax/error_reporter.gleam)
- [Source Snippet Implementation](../../src/syntax/source_snippet.gleam)
- [Core Error Formatter](../../src/core/error_formatter.gleam)
- [Rust Compiler Errors](https://github.com/rust-lang/rust/blob/master/compiler/rustc_errors/src)
- [Elm Compiler Errors](https://elm-lang.org/news/compiler-errors-for-humans)
