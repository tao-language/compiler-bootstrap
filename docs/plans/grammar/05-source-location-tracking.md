# Source Location Tracking

> **Goal**: Full source location tracking with filename, start/end positions (line/column)
> **Status**: ✅ Implemented - All phases complete
> **Date**: March 2025

---

## Status

### What's Working

- ✅ Token type includes `line` and `column` fields
- ✅ Lexer stores line/column in all tokens
- ✅ Position helper functions in grammar DSL
- ✅ Span type supports start/end positions (line/column)
- ✅ All grammar constructors use real positions
- ✅ All tests passing (256 tests)

### Implementation Complete

All 6 phases have been completed:

| Phase | Task | Status |
|-------|------|--------|
| 1 | Update Token type with line/column | ✅ Complete |
| 2 | Update lexer to store line/column | ✅ Complete |
| 3 | Add position helpers to grammar DSL | ✅ Complete |
| 4 | Update Span type with start/end | ✅ Complete |
| 5 | Update core syntax constructors | ✅ Complete |
| 6 | Update tests | ✅ Complete |

### Related

- See **[01-overview.md](./01-overview.md)** for grammar system overview
- See **[03-parser-library.md](./03-parser-library.md)** for parser details
- See **[../core/01-overview.md](../core/01-overview.md)** for core language status

---

## Motivation

Current implementation uses dummy spans:

```gleam
// Current (dummy span)
Term(Lam(name, body), Span("input", 0, 0))
```

This prevents:
- Accurate error messages ("error at line 5, column 10")
- IDE features (go to definition, hover tooltips)
- Source maps for debugging
- Underlining specific tokens in error output

---

## Design

### Token Type Enhancement

**Current:**
```gleam
pub type Token {
  Token(kind: String, value: String, start: Int, end: Int)
}
```

**Proposed:**
```gleam
pub type Token {
  Token(
    kind: String,
    value: String,
    start: Int,        // Character offset (0-based)
    end: Int,          // Character offset (0-based)
    line: Int,         // Line number (1-based)
    column: Int,       // Column number (1-based)
  )
}
```

### Span Type Enhancement

**Current:**
```gleam
pub type Span {
  Span(file: String, row: Int, col: Int)
}
```

**Proposed:**
```gleam
pub type Span {
  Span(
    file: String,
    start_line: Int,    // 1-based
    start_col: Int,     // 1-based
    end_line: Int,      // 1-based
    end_col: Int,       // 1-based
  )
}
```

### Position Helper Functions

Add to `src/syntax/grammar.gleam`:

```gleam
/// Extract span from first token in values
pub fn span_from_values(values: List(Value(a)), filename: String) -> Span {
  case values {
    [TokenValue(token), ..] -> span_from_token(token, filename)
    [AstValue(term), ..] -> term.span  // Assume term has .span field
    _ -> Span(filename, 1, 1, 1, 1)  // Default
  }
}

/// Create span from single token
pub fn span_from_token(token: Token, filename: String) -> Span {
  Span(
    file: filename,
    start_line: token.line,
    start_col: token.column,
    end_line: token.line,  // Single-line token
    end_col: token.column + int.length(token.value),
  )
}

/// Create span covering multiple tokens
pub fn span_from_tokens(
  first: Token,
  last: Token,
  filename: String,
) -> Span {
  Span(
    file: filename,
    start_line: first.line,
    start_col: first.column,
    end_line: last.line,
    end_col: last.column + int.length(last.value),
  )
}
```

### Grammar Constructor Pattern

**Current:**
```gleam
fn make_lambda(values) {
  case values {
    [_, TokenValue(name), _, AstValue(body)] ->
      Term(Lam(name, body), Span("input", 0, 0))
  }
}
```

**Future:**
```gleam
fn make_lambda(values) {
  case values {
    [lambda_token, TokenValue(name), dot_token, AstValue(body)] ->
      Term(
        Lam(name, body),
        grammar.span_from_tokens(lambda_token, dot_token, "input"),
      )
  }
}
```

---

## Implementation Plan

### Phase 1: Update Token Type

**File:** `src/syntax/lexer.gleam`

1. Add `line` and `column` fields to `Token` type
2. Update `tokenize()` to track and store positions
3. Update all token creation sites

**Estimated effort:** 1-2 hours

### Phase 2: Update Span Type

**File:** `src/core/core.gleam` (or `src/syntax/lexer.gleam` if moved)

1. Update `Span` type to support start/end positions
2. Update all `Span` construction sites
3. Add helper functions for span manipulation

**Estimated effort:** 2-3 hours

### Phase 3: Add Position Helpers to Grammar DSL

**File:** `src/syntax/grammar.gleam`

1. Add `span_from_values()` function
2. Add `span_from_token()` function
3. Add `span_from_tokens()` function
4. Export from module

**Estimated effort:** 1 hour

### Phase 4: Update Core Syntax Constructors

**File:** `src/core/syntax.gleam`

1. Update all constructor functions to use real positions
2. Pass filename through parse function
3. Update `parse()` to accept filename parameter

**Estimated effort:** 2-3 hours

### Phase 5: Update Tests

**File:** `test/core/syntax_test.gleam` and others

1. Update test expectations for real positions
2. Add tests for position tracking
3. Add tests for multi-line spans

**Estimated effort:** 1-2 hours

### Phase 6: Error Reporting Integration

**File:** `src/core/core.gleam` (error types)

1. Update error messages to use full spans
2. Add pretty-printing for spans (underline specific tokens)
3. Test error output

**Estimated effort:** 2-3 hours

**Total estimated effort:** 9-14 hours

---

## Example Usage

### Parsing with Filename

```gleam
import core/syntax

let source = "λx. x"
let result = syntax.parse_with_filename(source, "main.core")
// result.ast has spans with file="main.core"
```

### Error Reporting

```gleam
// Error output with full span
error: Type mismatch
  ┌─ main.core:5:10
  │
5 │ let x = λy. y + 1
  │           ^^^^^^^ Expected type Int, got Type0
```

### Multi-line Span

```gleam
// Lambda spanning multiple lines
let source = "
λx.
  x + 1
"
let result = syntax.parse(source)
// result.ast.span = Span("input", 2, 1, 3, 6)
```

---

## Migration Guide

### For Grammar Authors

**Before:**
```gleam
fn make_app(values) {
  case values {
    [AstValue(fun), _, AstValue(arg), _] ->
      Term(App(fun, arg), Span("input", 0, 0))
  }
}
```

**After:**
```gleam
fn make_app(values) {
  case values {
    [fun_token, _, arg_token, _] ->
      Term(
        App(fun, arg),
        grammar.span_from_tokens(fun_token, arg_token, "input"),
      )
  }
}
```

### For Error Reporting

**Before:**
```gleam
fn format_error(error) {
  case error {
    TypeMismatch(expected, got, span) ->
      "Type mismatch at " <> span.file <> ":" <> int.to_string(span.row)
  }
}
```

**After:**
```gleam
fn format_error(error) {
  case error {
    TypeMismatch(expected, got, span) ->
      "Type mismatch at " 
      <> span.file <> ":" 
      <> int.to_string(span.start_line) <> ":" 
      <> int.to_string(span.start_col)
  }
}
```

---

## Testing Strategy

### Unit Tests

```gleam
pub fn lexer_position_test() {
  let tokens = lexer.tokenize("λx. x")
  tokens |> should.equal([
    Token("Lambda", "λ", 0, 1, 1, 1),
    Token("Ident", "x", 1, 2, 1, 2),
    Token("Dot", ".", 2, 3, 1, 3),
    Token("Ident", "x", 4, 5, 1, 5),
  ])
}

pub fn multi_line_span_test() {
  let source = "λx.\n  x"
  let result = syntax.parse(source)
  case result.ast {
    Term(Lam(_, _), span) -> {
      span.start_line |> should.equal(1)
      span.end_line |> should.equal(2)
    }
    _ -> False |> should.be_true
  }
}
```

### Integration Tests

```gleam
pub fn error_position_test() {
  let source = "λx. x + y"
  let result = syntax.parse(source)
  // Should have error at position of '+'
  case result.errors {
    [ParseError(position, _, _), ..] -> {
      position |> should.equal(6)  // Position of '+'
    }
    _ -> False |> should.be_true
  }
}
```

---

## Benefits

1. **Accurate Error Messages** - Point to exact location
2. **IDE Support** - Go to definition, hover, etc.
3. **Source Maps** - Map compiled code back to source
4. **Better DX** - Underline specific tokens in errors
5. **Debugging** - Step through source, not AST

---

## Risks and Mitigations

### Risk: Breaking Changes to Span Type

**Mitigation:**
- Update all Span construction sites in single PR
- Provide migration helper functions
- Document changes clearly

### Risk: Performance Impact

**Mitigation:**
- Measure tokenization time before/after
- Line/column tracking is O(n) - same as current
- Span creation is O(1) - no impact

### Risk: Complexity in Constructors

**Mitigation:**
- Provide helper functions (`span_from_values`, etc.)
- Document common patterns
- Start with simple single-token spans

---

## References

- [Rust Span](https://doc.rust-lang.org/proc_macro/struct.Span.html)
- [TypeScript SourceFile](https://github.com/microsoft/TypeScript/wiki/Architectural-Overview#source-files)
- [Clang SourceLocation](https://clang.llvm.org/docs/InternalsManual.html#sourcelocation-sourcerange-and-fileid)
