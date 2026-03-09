# Error Reporter Specification

> **Goal**: Format errors with source locations and context
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Status

### What's Working

- Basic error message printing
- Parse error formatting

### What's Pending

- Source snippet formatting (like Rust compiler)
- Multi-line error contexts
- Hint suggestions
- Warning support (currently only errors)
- Full span information in errors

### Related

- See **[01-overview.md](./01-overview.md)** for overall CLI status
- See **[02-cli-parser.md](./02-cli-parser.md)** for argument parsing

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
    severity: Severity,
    message: String,
    span: Span,
    hint: Option(String),
  )
}
```

---

## Error Format

### Single-Line Error

```
error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32)
  │          ^^^^^^^^^ Expected $Type, got $I32
```

### Multi-Line Error

```
error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32) -> x
  │          ^^^^^^^^^
  │          │
  │          expected $Type here
  │
  = hint: Try using $Type instead
```

### Multiple Errors

```
error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32)
  │          ^^^^^^^^^ Expected $Type, got $I32

error: Undefined variable
  ┌─ example.core.tao:6:5
  │
6 │     y
  │     ^ Variable 'y' not in scope

Found 2 errors
```

---

## Reporter Implementation

```gleam
pub fn report(diagnostic: Diagnostic, source: String) -> formatter.Doc {
  let severity_doc = format_severity(diagnostic.severity)
  let message_doc = formatter.text(diagnostic.message)
  let location_doc = format_location(diagnostic.span)
  let snippet_doc = format_snippet(source, diagnostic.span)
  let hint_doc = case diagnostic.hint {
    Some(hint) -> formatter.concat([
      formatter.hardline,
      formatter.text("= hint: "),
      formatter.text(hint)
    ])
    None -> formatter.empty
  }
  
  formatter.concat([
    severity_doc,
    formatter.text(": "),
    message_doc,
    formatter.hardline,
    location_doc,
    formatter.hardline,
    snippet_doc,
    hint_doc
  ])
}

fn format_severity(severity: Severity) -> formatter.Doc {
  case severity {
    Error -> formatter.text("error")
    Warning -> formatter.text("warning")
    Info -> formatter.text("info")
  }
}

fn format_location(span: Span) -> formatter.Doc {
  formatter.concat([
    formatter.text("  ┌─ "),
    formatter.text(span.file),
    formatter.text(":"),
    formatter.int(span.start_line),
    formatter.text(":"),
    formatter.int(span.start_col)
  ])
}

fn format_snippet(source: String, span: Span) -> formatter.Doc {
  // Extract the relevant lines from source
  // Add line numbers and pointer to error location
  // Add underline for error span
}
```

---

## Source Snippet Formatting

### Extract Lines

```gleam
pub fn extract_lines(source: String, span: Span) -> List(Line) {
  let lines = string.split(source, "\n")
  let relevant_lines = 
    lines
    |> list.drop(span.start_line - 1)
    |> list.take(span.end_line - span.start_line + 1)
  
  relevant_lines
    |> list.index_map(fn(line, index) {
      Line(
        number: span.start_line + index,
        content: line,
        is_error_line: index == 0
      )
    })
}
```

### Add Line Numbers

```gleam
pub fn format_lines(lines: List(Line)) -> formatter.Doc {
  let max_width = get_max_line_number_width(lines)
  
  lines
    |> list.map(fn(line) {
      formatter.concat([
        formatter.right_pad(formatter.int(line.number), max_width),
        formatter.text(" │ "),
        formatter.text(line.content),
        case line.is_error_line {
          True => formatter.hardline
          False => formatter.empty
        }
      ])
    })
    |> formatter.concat_all
}
```

### Add Error Pointer

```gleam
pub fn format_pointer(span: Span, message: String) -> formatter.Doc {
  formatter.concat([
    formatter.text("  │ "),
    formatter.string_repeat(" ", span.start_col - 1),
    formatter.text("^"),
    formatter.string_repeat("^", span.end_col - span.start_col),
    case message {
      "" -> formatter.empty
      _ -> formatter.concat([
        formatter.text(" "),
        formatter.text(message)
      ])
    }
  ])
}
```

---

## Error Messages

### Parse Errors

```
error: Unexpected token
  ┌─ example.core.tao:3:5
  │
3 │   λx. x
  │     ^ Expected identifier, got '.'
```

```
error: Unexpected end of file
  ┌─ example.core.tao:5:1
  │
5 │ λx.
  │    ^ Expected expression after '.'
```

### Type Errors

```
error: Type mismatch
  ┌─ example.core.tao:5:10
  │
5 │ let x = (x : $I32)
  │          ^^^^^^^^^ Expected $Type, got $I32
```

```
error: Occurs check failed
  ┌─ example.core.tao:3:1
  │
3 │ λf. f(f)
  │ ^^^^^^^^ Infinite type: a = a -> b
```

```
error: Unbound variable
  ┌─ example.core.tao:2:5
  │
2 │     x
  │     ^ Variable 'x' not in scope
```

### Runtime Errors

```
error: Division by zero
  ┌─ example.core.tao:3:10
  │
3 │ let x = 10 / 0
  │          ^^^^^ Evaluated to division by zero
```

---

## Warning Messages

```
warning: Unused variable
  ┌─ example.core.tao:2:5
  │
2 │ let x = 5
  │     ^ This variable is never used
  │
  = hint: Consider removing it or prefixing with '_'
```

```
warning: Redundant type annotation
  ┌─ example.core.tao:3:10
  │
3 │ let x: Int = 5
  │          ^^^ Type can be inferred
```

---

## Testing

```gleam
pub fn report_type_error_test() {
  let source = "let x = (x : $I32)"
  let diagnostic = Diagnostic(
    severity: Error,
    message: "Type mismatch",
    span: Span("test.core.tao", 1, 10, 1, 15),
    hint: Some("Try using $Type instead"),
  )
  
  let doc = report(diagnostic, source)
  let output = formatter.render(doc, 80)
  
  // Check that output contains expected elements
  output |> should.contain("error: Type mismatch")
  output |> should.contain("test.core.tao:1:10")
  output |> should.contain("Expected $Type, got $I32")
  output |> should.contain("hint: Try using $Type instead")
}

pub fn report_parse_error_test() {
  let source = "λx. x"
  let diagnostic = Diagnostic(
    severity: Error,
    message: "Unexpected token",
    span: Span("test.core.tao", 1, 3, 1, 4),
    hint: None,
  )
  
  let doc = report(diagnostic, source)
  let output = formatter.render(doc, 80)
  
  output |> should.contain("error: Unexpected token")
  output |> should.contain("Expected identifier, got '.'")
}
```

---

## See Also

- **[01-overview.md](./01-overview.md)** - CLI overview
- **[02-cli-parser.md](./02-cli-parser.md)** - Argument parsing
- **[../core/02-syntax.md](../core/02-syntax.md)** - Core language syntax
