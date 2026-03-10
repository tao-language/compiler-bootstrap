# Error Reporter Specification

> **Goal**: Format errors with source locations and context
> **Status**: ✅ Phase 1 & 2 Complete - Parse and Type errors display with source snippets
> **Date**: March 2025

---

## Status

### What's Working

- ✅ Source snippet formatter (`syntax/source_snippet.gleam`)
- ✅ Error reporter module (`syntax/error_reporter.gleam`)
- ✅ Parse error to diagnostic conversion
- ✅ Type error to diagnostic conversion
- ✅ Multi-span error support (type mismatches)
- ✅ Error codes (E0001, E0101-E0106, E0201-E0202, E0301)
- ✅ Hints for all error types
- ✅ Source snippet display with line numbers and pointers
- ✅ CLI integration for both parse and type errors
- ✅ All 401 tests passing

### What's Pending

- 📋 JSON error output format (`--error-format=json`)
- 📋 Color terminal support (`--color=auto/always/never`)
- 📋 Context lines (show surrounding code)
- 📋 Proper exit codes
- 📋 Warning support (currently only errors)

### Related

- See **[01-overview.md](./01-overview.md)** for overall CLI status
- See **[02-cli-parser.md](./02-cli-parser.md)** for argument parsing
- See **[../error-reporting/01-overview.md](../error-reporting/01-overview.md)** for error reporting system

---

## Diagnostic Types

```gleam
pub type Severity {
  Error
  Warning
  Info
}

pub type Diagnostic {
  Diagnostic(
    code: String,           // e.g., "E0001"
    severity: Severity,
    message: String,
    primary_span: Span,
    spans: List(Highlight), // Secondary spans
    notes: List(String),
    hints: List(String),
  )
}

pub type Highlight {
  Highlight(
    span: Span,
    style: HighlightStyle,  // Primary or Secondary
    label: Option(String),
  )
}
```

---

## Error Format

### Parse Error (Single-Line)

```
error[E0001]: Unexpected token
  ┌─ example.core.tao:1:1
1 │ {{{
    ^
2 │
  = note: Expected: valid alternative
  = note: Got: none
  = hint: Check syntax near this position
```

### Type Error (Multi-Span)

```
error[E0101]: Type mismatch
  ┌─ input:1:1
1 │ 42 : $Type
    ^^ ----
2 │
  = hint: Check that types are compatible
```

### Undefined Variable

```
error[E0102]: Undefined variable
  ┌─ example.core.tao:1:8
1 │ x -> y
    │    ^
2 │
  = hint: Check variable name and scope
```

### Unsolved Hole

```
error[E0106]: Unsolved hole
  ┌─ example.core.tao:1:5
1 │ x -> ?
    │    ^
2 │
  = note: Hole #0 was not solved during type checking
  = hint: Provide a type annotation or check your term
```

### Multiple Errors

```
error[E0001]: Unexpected token
  ┌─ example.core.tao:1:1
1 │ {{{
    ^
2 │
  = note: Expected: valid alternative
  = note: Got: none
  = hint: Check syntax near this position

Found 1 error
```

---

## Error Codes

| Code | Category | Description |
|------|----------|-------------|
| E0001 | Parse | Unexpected token |
| E0101 | Type | Type mismatch |
| E0102 | Type | Undefined variable |
| E0103 | Type | Not a function |
| E0104 | Type | Arity mismatch |
| E0105 | Type | Undefined constructor |
| E0106 | Type | Unsolved hole |
| E0201 | Pattern | Missing match case |
| E0202 | Pattern | Redundant match case |
| E0301 | Runtime | Permission denied |
| E9999 | Type | Unknown type error (fallback) |

---

## Reporter Implementation

The error reporter is implemented in `src/syntax/error_reporter.gleam`:

```gleam
// Convert parse errors to diagnostics
pub fn parse_error_to_diagnostic(
  error: grammar.ParseError,
  source: String,
  file: String,
) -> source_snippet.Diagnostic { ... }

// Convert type errors to diagnostics
pub fn type_error_to_diagnostic(
  error: core.Error,
  source: String,
  file: String,
) -> source_snippet.Diagnostic { ... }

// Format diagnostic for display
pub fn format_diagnostic(
  diagnostic: source_snippet.Diagnostic,
  source: String,
) -> String { ... }
```

---

## Testing

Error reporting is tested through:

1. **Example files** in `examples/core/errors/`:
   - `syntax_errors/01_unexpected_token.core.tao` - Parse error example
   - `syntax_errors/02_malformed_match.core.tao` - Malformed match expression
   - `type_errors/01_param_type_mismatch.core.tao` - Type mismatch example
   - `type_errors/02_annotation_mismatch.core.tao` - Annotation mismatch example

2. **Manual testing** with CLI:
   ```bash
   gleam run check examples/core/errors/syntax_errors/01_unexpected_token.core.tao
   gleam run check examples/core/errors/type_errors/01_param_type_mismatch.core.tao
   ```

3. **Unit tests** - 401 tests passing

4. **Build status**:
   - ✅ Compiles successfully
   - ✅ 401 tests passing
   - ⚠️ Minor warnings (unused imports - being cleaned up)

---

## Future Enhancements

### Phase 4: Full Error Codes and Suggestions
- [x] Error codes for parse errors (E0001)
- [x] Error codes for type errors (E0101-E0106)
- [x] Error codes for pattern errors (E0201-E0202)
- [x] Error codes for runtime errors (E0301)
- [x] Basic hints for all error types
- [ ] More specific hints based on error context
- [ ] "Did you mean?" suggestions

### Phase 5: JSON Output
- [ ] `--error-format=json` flag
- [ ] Machine-readable error output
- [ ] IDE integration support

### Phase 6: Polish
- [ ] `--color=auto/always/never` flag
- [ ] Context lines (show surrounding code)
- [ ] Proper exit codes (requires FFI)
- [ ] Warning support with `--warn` flag
- [ ] Clean up unused imports
