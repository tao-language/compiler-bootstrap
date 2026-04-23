# Parse Error Panic Fix Plan

> **Goal**: Fix parse error handling to display source snippets instead of panicking
> **Status**: ✅ RESOLVED - All 401 tests passing, Phase 1 & 2 complete
> **Date**: March 2025

---

## Solution Implemented

The parser now uses an **error AST** approach:

1. **Error AST Nodes**: Added `Term.Err` and `NamedTerm.NErr` variants to represent parse errors in the AST
2. **Error AST Parameter**: `grammar.parse()` now takes an `error_ast` parameter of type `a` to use when parsing fails
3. **No Panics**: The parser never panics on user input - it always returns a valid AST (possibly containing error nodes) along with an error list
4. **Error Reporter**: New module `syntax/error_reporter.gleam` converts errors to diagnostics with source snippets
5. **CLI Integration**: Both parse and type errors display with source snippets, error codes, and hints

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

// Error reporter converts to diagnostics
pub fn parse_error_to_diagnostic(error, source, file) -> Diagnostic { ... }
pub fn type_error_to_diagnostic(error, source, file) -> Diagnostic { ... }
```

### Benefits

- ✅ Parser never panics on user input
- ✅ Always returns valid AST for further processing
- ✅ Errors are collected and can be displayed together
- ✅ Enables error recovery and IDE features
- ✅ CLI works correctly with both valid and invalid files
- ✅ Source snippets show exact error location
- ✅ Error codes for easy reference (E0001, E0101, etc.)
- ✅ Hints help users fix errors quickly

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
- ✅ CLI works correctly with parse errors
- ✅ CLI works correctly with type errors
- ✅ All 401 tests passing
- ✅ Phase 1 complete: Parse error display
- ✅ Phase 2 complete: Type error display
- ✅ Phase 3 complete: Multi-span support
- 📋 Phase 4 pending: Full error codes and suggestions
- 📋 Phase 5 pending: JSON output format
- 📋 Phase 6 pending: Exit codes, color, context lines

### Example Output

**Parse Error:**
```
error[E0001]: Unexpected token
  ┌─ examples/core/errors/syntax_errors/01_unexpected_token.core.tao:1:1
1 │ {{{
    ^
2 │
  = note: Expected: valid alternative
  = note: Got: none
  = hint: Check syntax near this position
```

**Type Error:**
```
error[E0101]: Type mismatch
  ┌─ input:1:1
1 │ 42 : $Type
    ^^ ----
2 │
  = hint: Check that types are compatible
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration (Phase 1 & 2 complete)
