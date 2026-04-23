# Error Handling Design

## Design Philosophy

1. **Error resilience everywhere** — Every phase continues after errors
2. **Accumulate, don't stop** — All errors are collected and reported together
3. **Span-safe** — Every error has an accurate source location
4. **Graceful degradation** — Partial results are still returned (even with errors)
5. **Clear diagnostics** — Errors include explanations, hints, and context

## Error Accumulation Pattern

Every function returns `(result, errors)` tuples. This makes error accumulation explicit and type-safe:

```gleam
pub type Result(a, e) {
  Ok(a, List(e))  // (result, errors_found)
}
```

**Key principle:** Never use `panic` or `abort` on errors. Always return the result with attached errors.

## Phase-by-Phase Error Handling

### 1. Parse Errors (syntax/error_reporter.gleam)

```gleam
/// Parse error with full diagnostic information
pub type ParseError {
  ParseError(
    span: Span,           // Where the error occurred
    expected: String,     // What the parser expected
    got: String,          // What it actually found
    context: String,      // Additional context (e.g., "in expression", "at module level")
  )
}

/// Parse result with accumulated errors
pub type ParseResult(a) {
  ParseResult(
    ast: a,               // Partial AST (may contain error nodes)
    errors: List(ParseError),  // ALL parse errors found
  )
}
```

**Error recovery strategy:**
- At module level: try each statement independently; continue after errors
- At expression level: try each alternative independently; continue after errors
- Create synthetic AST nodes for errors (with `ParseError` attached via `ast_string`)
- Don't backtrack — the next token after an error is the recovery point

### 2. Type Errors (core/error_formatter.gleam)

```gleam
/// All possible type errors
pub type TypeError {
  TypeMismatch(expected: Value, got: Value, expected_span: Span, got_span: Span)
  VarUndefined(index: Int, span: Span)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(fun: Term, fun_type: Value, span: Span)
  ArityMismatch(expected: Int, actual: Int, fn_span: Span, call_span: Span)
  CtrUndefined(tag: String, span: Span)
  InfiniteType(hole_id: Int, ty: Value, self_span: Span, ctx_span: Span)
  RcdMissingFields(fields: List(String), span: Span)
  CtrUnsolvedParam(tag: String, id: Int, span: Span)
  DotFieldNotFound(name: String, available: List(String), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  SpineMismatch(expected: Value, actual: Value, fn_span: Span, call_span: Span)
  PatternMismatch(pattern: Pattern, expected_type: Value, pattern_span: Span, value_span: Span)
  MatchMissingCase(span: Span, missing_pattern: String)
  MatchRedundantCase(span: Span)
  ComptimePermissionDenied(operation: String, required: List(String), span: Span)
  TODO(message: String)
  NameShadow(name: String, first_span: Span, second_span: Span)
  SyntaxError(span: Span, expected: String, got: String, context: String)
}
```

**Type error accumulation:**
- Errors are stored in `State.errors: List(TypeError)`
- Every type-checking function updates `State` (never returns early)
- The final state contains all errors found during type checking

### 3. Import Errors (tao/error_reporter.gleam)

```gleam
/// Import resolution errors
pub type ImportError {
  ModuleNotFound(path: String, span: Span)
  CircularImport(from: String, to: String, span: Span)
  ParseError(path: String, errors: List(ParseError))
  TypeError(path: String, errors: List(TypeError))
  NameNotFound(name: String, available: List(String), span: Span)
}
```

**Import error recovery:**
- If a module fails to load, create an error binding that produces `Err("module not found")`
- Continue compiling the rest of the module
- Report all import errors together

## Error Reporting

### Diagnostic Format

```gleam
/// A formatted diagnostic message with source context
pub type Diagnostic {
  Diagnostic(
    code: String,           // Error code (e.g., "E0101")
    severity: Severity,     // Error, Warning, Info
    message: String,        // Primary message
    primary_span: Span,     // Where the error is
    spans: List(Highlight), // Additional spans with labels
    notes: List(String),    // Additional notes
    hints: List(String),    // Suggestions for fixing
  )
}

pub type Severity {
  Error
  Warning
  Info
}

pub type Highlight {
  Highlight(
    span: Span,
    style: Style,    // Primary, Secondary, Help
    label: Option(String),  // Optional label
  )
}

pub type Style {
  Primary
  Secondary
  Help
}
```

### Format Diagnostic

```gleam
/// Format a diagnostic as a human-readable string with source context
pub fn format_diagnostic(diagnostic: Diagnostic, source: String) -> String {
  let header = format_header(diagnostic)
  let spans = format_spans(diagnostic.primary_span, diagnostic.spans, source)
  let message = format_message(diagnostic.message, source)
  let notes = format_list("Note:", diagnostic.notes)
  let hints = format_list("Hint:", diagnostic.hints)
  
  header <> "\n" <> spans <> "\n" <> message <> "\n" <> notes <> "\n" <> hints
}

/// Format error header with code and severity
fn format_header(diagnostic: Diagnostic) -> String {
  case diagnostic.severity {
    Error -> "error[" <> diagnostic.code <> "]: " <> diagnostic.message
    Warning -> "warning[" <> diagnostic.code <> "]: " <> diagnostic.message
    Info -> "info[" <> diagnostic.code <> "]: " <> diagnostic.message
  }
}

/// Format source spans with line numbers and highlighting
fn format_spans(primary: Span, highlights: List(Highlight), source: String) -> String {
  let lines = string.split(source, "\n")
  let primary_line = get_line(lines, primary.start_line)
  
  let marker = string.repeat(" ", primary.start_col) <> string.repeat("^", primary.end_col - primary.start_col)
  
  "  " <> int.to_string(primary.start_line) <> " | " <> primary_line
  <> "\n  " <> marker <> "\n"
}

/// Format a list of notes or hints
fn format_list(label: String, items: List(String)) -> String {
  case items {
    [] -> ""
    _ -> "\n" <> label <> ":\n" <> list.map(items, fn(item) -> "    " <> item) |> string.join("\n")
  }
}
```

### Example Output

```
error[E0101]: Type mismatch
  ┌─ main.tao:5:12
  │
5 │   let x: Int = "hello"
  │            ^   -------- expected Int, got String
  │            │
  │            this value has type String

note: String and Int are incompatible types
hint: Check that the expression has the expected type
hint: Consider adding a type annotation
```

## Error Codes

| Code | Phase | Description |
|------|-------|-------------|
| E0001 | Parse | Syntax error |
| E0002 | Parse | Unexpected token |
| E0003 | Parse | Unclosed delimiter |
| E0101 | Type | Type mismatch |
| E0102 | Type | Undefined variable |
| E0103 | Type | Cannot call non-function |
| E0104 | Type | Wrong arity |
| E0105 | Type | Constructor not found |
| E0106 | Type | Unsolved hole |
| E0107 | Type | Infinite type |
| E0108 | Type | Missing record fields |
| E0110 | Type | Field not found |
| E0201 | Pattern | Pattern type mismatch |
| E0202 | Pattern | Match not exhaustive |
| E0203 | Pattern | Redundant pattern |
| E0301 | Import | Module not found |
| E0302 | Import | Circular import |
| E0303 | Import | Name not found in module |
| E0501 | Comptime | Permission denied |

## Error Propagation

```gleam
/// Collect errors from multiple phases
pub fn collect_errors(results: List(Result(a, e))) -> List(e) {
  results
  |> list.map(fn(r) -> case r { Ok(_, errors) -> errors })
  |> list.concat
}

/// Continue with a result even if there are errors
pub fn continue_with_errors(result: Result(a, e)) -> a {
  case result {
    Ok(value, _) -> value
    Error(err) -> panic as "Error in " <> show(err)  // Should not happen
  }
}

/// Create an error result from a partial result
pub fn error_result(partial: a, errors: List(e)) -> Result(a, e) {
  Ok(partial, errors)
}
```

## Testable Error Cases

### Parse Error Test

```gleam
should("accumulate parse errors for multiple syntax errors") {
  let source = """
    fn foo(x
    let bar = 
    type Baz
  """
  
  let result = parse(source)
  result.errors.length >= 3
  
  // Each error should have:
  for err in result.errors {
    err.span.start_line > 0
    err.expected != ""
    err.got != ""
  }
}
```

### Type Error Test

```gleam
should("accumulate type errors for multiple type mismatches") {
  let source = """
    let x: Int = "hello"
    let y: String = 42
    let z: Int = true
  """
  
  let result = compile_core(source)
  result.errors.length >= 3  // At least 3 type errors
}
```

### Import Error Test

```gleam
should("detect circular imports") {
  let mod_a = "import b { foo }"
  let mod_b = "import a { bar }"
  
  let result = compile_with_modules(#(mod_a, mod_b))
  case result {
    Error(CircularImport(_, _, _)) -> True
    _ -> False
  }
}
```

### Error Span Accuracy Test

```glem
should("produce accurate spans for type errors") {
  let source = "let x: Int = 3.14"
  let result = compile_core(source)
  
  case result.errors {
    [err] ->
      err.span.start_line == 1
      err.span.start_col == 17  // Position of "3.14"
      err.span.end_col == 21
    _ -> False
  }
}
```
