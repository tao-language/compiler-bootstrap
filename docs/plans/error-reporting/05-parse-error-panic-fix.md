# Parse Error Panic Fix Plan

> **Goal**: Fix parse error handling to display source snippets instead of panicking
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Problem

When a parse error occurs, the compiler panics with a message like:
```
Parse error: expected valid alternative, got none at position 0
```

Instead of showing a nice source snippet:
```
error[E0001]: Unexpected token
   ┌─ file.core.tao:1:1
   │
 1 │ {{{
   │ ^
   │
   = expected: expression
   = got:      '{'
```

## Root Cause

Gleam uses strict evaluation. When constructing a `ParseResult(a)`:

```gleam
ParseResult(ast: panic as msg, errors: [ParseError(...)])
```

The `panic as msg` expression is evaluated IMMEDIATELY during construction, before the caller can check `errors`.

This is fundamental to Gleam's evaluation model - all function arguments are evaluated before the function is called.

---

## Solution Approaches

### Approach 1: Lazy AST Field (Not Possible in Gleam)

In a lazy language, we could defer the panic:
```gleam
// This doesn't work in Gleam
ParseResult(ast: lazy(panic as msg), errors: [...])
```

**Status**: ❌ Not possible in Gleam

---

### Approach 2: Result Type Instead of ParseResult

Change from:
```gleam
pub type ParseResult(a) {
  ParseResult(ast: a, errors: List(ParseError))
}
```

To:
```gleam
pub type ParseResult(a) {
  Success(a)
  Failure(List(ParseError))
}
```

**Pros:**
- Clean separation of success/failure
- No panic on error
- Type-safe (can't access AST on failure)

**Cons:**
- Breaking change - all call sites need updating
- Loses partial AST information (sometimes useful for error recovery)

**Implementation Steps:**
1. Update `syntax/grammar.gleam` ParseResult type
2. Update `core/syntax.gleam` parse function
3. Update `compiler_bootstrap.gleam` check_core function
4. Update all test files

**Estimated Effort**: 2-3 hours

---

### Approach 3: Option Type for AST

```gleam
pub type ParseResult(a) {
  ParseResult(ast: Option(a), errors: List(ParseError))
}
```

**Pros:**
- Less breaking than Approach 2
- Explicit about AST availability

**Cons:**
- Still requires checking Option before access
- `None` with errors is similar to Failure

**Status**: 📋 Viable alternative

---

### Approach 4: Two-Phase Parsing

Phase 1: Quick validation (returns `Result(Nil, List(ParseError))`)
Phase 2: Full parse (only if phase 1 succeeds)

```gleam
pub fn validate(source: String) -> Result(Nil, List(ParseError)) {
  // Quick validation without building AST
}

pub fn parse(source: String) -> ParseResult(Term) {
  // Full parse - only called after validate succeeds
}
```

**Pros:**
- Clean separation
- Can show errors without AST

**Cons:**
- Duplicates work (parse twice)
- API change for all callers

**Status**: 📋 Viable but inefficient

---

### Approach 5: Error-First ParseResult

```gleam
pub type ParseResult(a) {
  ParseResult(errors: List(ParseError), get_ast: fn() -> a)
}
```

The AST is a thunk that only panics if called when there are errors.

**Pros:**
- Lazy AST evaluation
- Backwards compatible API

**Cons:**
- Unusual pattern for Gleam
- Still panics if caller ignores errors

**Status**: 📋 Creative but complex

---

## Recommended Approach

**Approach 2** (Result Type) is the cleanest and most idiomatic:

```gleam
pub type ParseResult(a) {
  Success(a)
  Failure(List(ParseError))
}

pub fn parse(grammar: Grammar(a), source: String) -> ParseResult(a) {
  case parse_rule(...) {
    Ok(#(ast, _)) -> Success(ast)
    Error(err) -> Failure([err])
  }
}
```

Usage:
```gleam
case syntax.parse(source) {
  Success(ast) -> { /* use ast */ }
  Failure(errors) -> { /* show errors */ }
}
```

---

## Implementation Checklist

- [ ] Update `syntax/grammar.gleam` ParseResult type
- [ ] Update `syntax/grammar.parse` function
- [ ] Update `core/syntax.gleam` parse function
- [ ] Update `core/syntax.named_to_de_bruijn` integration
- [ ] Update `compiler_bootstrap.gleam` check_core function
- [ ] Update error_reporter integration
- [ ] Update all test files (39 occurrences of `syntax.parse`)
- [ ] Test with valid files
- [ ] Test with invalid files
- [ ] Verify source snippets display correctly

---

## Success Criteria

- ✅ Parse errors show source snippets with highlights
- ✅ No panics on invalid input
- ✅ All 401+ tests pass
- ✅ Error messages include:
  - Source location
  - Source snippet with pointer
  - Expected vs got
  - Helpful suggestions

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration
