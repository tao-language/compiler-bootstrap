# Error Reporting Plan

> **Goal**: Provide clear, actionable error messages with source snippets that help both humans and AI assistants quickly understand and fix errors
> **Status**: ✅ Core Infrastructure Complete - All 401 tests passing
> **Date**: March 2025

---

## Core Principle

**Every error message should answer three questions:**

1. **What went wrong?** - Clear description of the problem
2. **Where is it?** - Precise source location with visual snippet
3. **How do I fix it?** - Actionable suggestion or hint

---

## Implementation Status

### What's Working

- ✅ Source snippet formatter module (`syntax/source_snippet.gleam`)
- ✅ Enhanced parse error types with spans (`ParseErrorWithSpan`)
- ✅ Error reporter module (`syntax/error_reporter.gleam`)
- ✅ CLI integration for parse errors
- ✅ Type error formatting (basic)
- ✅ Error AST nodes (`Term.Err`, `NamedTerm.NErr`) for graceful error recovery
- ✅ Parser never panics - always returns valid AST with error list
- ✅ All 401 tests passing
- ✅ Fixed critical bug: `[..]` pattern matching (matched empty lists incorrectly)

### What's Pending

- 📋 Source snippet display in CLI (infrastructure ready, integration needed)
- 📋 Multi-span error display (e.g., type mismatches)
- 📋 Error codes for all error types (E0001, E0101, etc.)
- 📋 Suggestions/hints for common errors
- 📋 JSON error output format
- 📋 Color terminal support
- 📋 Context lines (show surrounding code)

### Bug Fixed

**Pattern Matching Bug**: The `[..]` pattern in Gleam matches ANY list, including empty lists. Changed to `[_, ..]` to only match non-empty lists. This was causing parse errors to be reported even when parsing succeeded.

---

## Error Categories

### Parse Errors

| Error | Code | Description |
|-------|------|-------------|
| Unexpected token | `E0001` | Parser encountered unexpected token |
| Missing token | `E0002` | Expected token not found |
| Invalid syntax | `E0003` | Syntax doesn't match any rule |

### Type Errors

| Error | Code | Description |
|-------|------|-------------|
| Type mismatch | `E0101` | Expected type A, got type B |
| Undefined variable | `E0102` | Variable not in scope |
| Not a function | `E0103` | Applied non-function |
| Arity mismatch | `E0104` | Wrong number of arguments |
| Infinite type | `E0105` | Occurs check failed |
| Unsolved hole | `E0106` | Metavariable not unified |

### Pattern Match Errors

| Error | Code | Description |
|-------|------|-------------|
| Missing case | `E0201` | Pattern match not exhaustive |
| Redundant case | `E0202` | Unreachable pattern |
| Pattern mismatch | `E0203` | Pattern doesn't match type |

### Runtime Errors

| Error | Code | Description |
|-------|------|-------------|
| Permission denied | `E0301` | Comptime operation not allowed |
| Division by zero | `E0302` | Runtime arithmetic error |

---

## Example Error Messages

### Type Mismatch (Before)

```
Type mismatch: expected <type>, got <type>
```

### Type Mismatch (After)

```
error[E0101]: Type mismatch
   ┌─ src/example.core.tao:5:10
   │
 5 │ let result = (x : $I32) -> x
   │              ^^^^^^^^^
   │
   = expected: $Type
   = got:      $I32
   │
   = note: Function parameters must have type $Type
   = hint: Try using $Type instead of $I32
   = help: See https://docs.example.com/errors/E0101
```

### Undefined Variable (Before)

```
Undefined variable at (1:8)
```

### Undefined Variable (After)

```
error[E0102]: Undefined variable
   ┌─ src/example.core.tao:1:8
   │
 1 │ x -> y
   │        ^
   │
   = 'y' is not defined in this scope
   │
   = note: Variables must be bound by a lambda or pattern
   = help: Did you mean to use 'x' instead?
```

### Missing Pattern Case (Before)

```
Missing match case at (3:1)
```

### Missing Pattern Case (After)

```
error[E0201]: Missing pattern case
   ┌─ src/example.core.tao:3:1
   │
 3 │ %match opt ~ $Type {
   │ ^^^^^^^^^^^^^^^^^^^^
 4 │   | #Some(x) -> x
   │   ───────────────
 5 │ }
   │ ─
   │
   = pattern '#None' not covered
   │
   = note: The type 'Option' has these constructors:
           - #Some
           - #None
   = help: Add a case for '#None':
           | #None -> <default_value>
```

---

## Related Documents

- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[03-source-snippets.md](./03-source-snippets.md)** - Source snippet formatting
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration plan
- **[../core/01-overview.md](../core/01-overview.md)** - Core language overview

---

## Success Criteria

- ✅ All errors show source snippets with pointers
- ✅ Multi-span errors display all relevant locations
- ✅ Every error has a unique code (E####)
- ✅ Common errors include helpful suggestions
- ✅ JSON output available for IDE integration
- ✅ Error documentation at stable URLs
- ✅ Errors tested with golden files

---

## Implementation Phases

### Phase 1: Foundation (Week 1)
- [ ] Source snippet formatter
- [ ] Error code assignment
- [ ] Basic suggestion system

### Phase 2: Enhancement (Week 2)
- [ ] Multi-span error display
- [ ] Context lines (surrounding code)
- [ ] Color terminal support

### Phase 3: Polish (Week 3)
- [ ] JSON output format
- [ ] Error documentation website
- [ ] Golden file tests

### Phase 4: Integration (Week 4)
- [ ] IDE integration guide
- [ ] AI assistant optimization
- [ ] User feedback incorporation
