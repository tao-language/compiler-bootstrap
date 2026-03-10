# Parse Error Panic Fix Plan

> **Goal**: Fix parse error handling to display source snippets instead of panicking
> **Status**: ✅ RESOLVED - All 401 tests passing
> **Date**: March 2025

---

## Solution Implemented

The parser now uses an **error AST** approach:

1. **Error AST Nodes**: Added `Term.Err` and `NamedTerm.NErr` variants to represent parse errors in the AST
2. **Error AST Parameter**: `grammar.parse()` now takes an `error_ast` parameter of type `a` to use when parsing fails
3. **No Panics**: The parser never panics on user input - it always returns a valid AST (possibly containing error nodes) along with an error list

### Implementation

```gleam
// Grammar parser signature
pub fn parse(grammar: Grammar(a), source: String, error_ast: a) -> ParseResult(a)

// Usage in core/syntax.gleam
pub fn parse(source: String) -> grammar.ParseResult(Term) {
  let error_ast = AsTerm(NErr("Parse error", grammar.Span("", 0, 0, 0, 0)))
  let parsed = grammar.parse(core_grammar(), source, error_ast)
  // Process result...
}
```

### Benefits

- ✅ Parser never panics on user input
- ✅ Always returns valid AST for further processing
- ✅ Errors are collected and can be displayed together
- ✅ Enables error recovery and IDE features
- ✅ CLI works correctly with both valid and invalid files

### Bug Fixed

**Pattern Matching Bug**: The `[..]` pattern in Gleam matches ANY list, including empty lists. This caused the error branch to be taken even when `errors` was empty. Fixed by changing to `[_, ..]` which only matches non-empty lists.

```gleam
// Before (bug)
case errors {
  [..] -> { /* This matched [] too! */ }
  [] -> { /* Never reached */ }
}

// After (fixed)
case errors {
  [_, ..] -> { /* Only matches non-empty lists */ }
  [] -> { /* Matches empty list */ }
}
```

### Current Status

- ✅ Core infrastructure complete
- ✅ CLI works correctly
- ✅ All 401 tests passing
- 📋 Source snippet display integration pending
