# Source Snippet Formatting

> **Goal**: Display source code with precise highlighting to show exactly where errors occur
> **Status**: 📋 Planned
> **Date**: March 2025

---

## Overview

Source snippets are the visual representation of errors in the source code. They should:

1. **Show the exact location** - Precise character-level highlighting
2. **Provide context** - Show surrounding lines
3. **Be scannable** - Easy to understand at a glance
4. **Work in all terminals** - Graceful degradation for color/unicode

---

## Anatomy of a Source Snippet

```
   ┌─ src/file.core.tao:3:5
   │
 3 │ let x : $Type(1) = 42
   │       ^^^^^^^^^^
   │
 2 │ let y = 1
   │     ─
   │
   = expected: $Type
```

### Components

| Part | Description | Example |
|------|-------------|---------|
| Header | File and location | `src/file.core.tao:3:5` |
| Ruler | Vertical guide | `│` |
| Line numbers | For reference | `3 │` |
| Source line | The actual code | `let x : $Type(1) = 42` |
| Pointer | Highlights error | `^^^^^^^^^^` |
| Margin note | Additional context | `─` on line 2 |
| Footer | Explanations | `= expected: $Type` |

---

## Implementation

### Core Data Structure

```gleam
pub type SourceSnippet {
  SourceSnippet(
    file: String,           // File path
    line: Int,              // Primary line (1-based)
    column: Int,            // Primary column (1-based)
    source: String,         // Full source file
    highlights: List(Highlight), // What to highlight
    context_lines: Int,     // Lines before/after to show
  )
}

pub type Highlight {
  Highlight(
    start_line: Int,
    start_col: Int,
    end_line: Int,
    end_col: Int,
    style: HighlightStyle,
    label: Option(String),
  )
}

pub type HighlightStyle {
  Primary      // Main error location (^^^)
  Secondary    // Related location (───)
  Context      // Just showing context
}
```

### Formatting Algorithm

```gleam
pub fn format_snippet(snippet: SourceSnippet) -> String {
  let lines = get_relevant_lines(snippet)
  let max_line_num = get_max_line_number(lines)
  
  lines
  |> list.map(fn(line) {
    format_line(line, snippet.highlights, max_line_num)
  })
  |> string.join("\n")
}
```

---

## Multi-Span Errors

For errors with multiple locations (e.g., type mismatches):

```
error[E0101]: Type mismatch
   ┌─ src/example.core.tao:5:10
   │
 5 │ let f = (x : $I32) -> x
   │              ────
   │              │
   │              expected type is $Type
   │
 6 │ let arg = 42
   │           ^^
   │           │
   │           argument has type $I32
   │
   = note: Function parameter types must be $Type
```

### Implementation

```gleam
pub type MultiSpanSnippet {
  MultiSpanSnippet(
    file: String,
    spans: List(#(Span, SpanLabel)),
    message: String,
  )
}

pub type SpanLabel {
  SpanLabel(
    text: String,        // Label text
    style: HighlightStyle,
  )
}
```

---

## Edge Cases

### Very Long Lines

Truncate and add ellipsis:

```
   │
 5 │ let veryLongVariableName = fn(x) { ...super long expression... }
   │     ──────────────────────
   │
```

```gleam
fn truncate_line(line: String, max_width: Int) -> String {
  case string.length(line) > max_width {
    True -> string.slice(line, 0, max_width - 3) <> "..."
    False -> line
  }
}
```

### Multi-Line Highlights

```
   │
 3 │ %match x ~ $Type {
   │ ─────────────────^
 4 │   | #Some(y) -> y
   │   ───────────────
 5 │ }
   │ ─
   │
   = missing case for #None
```

### Unicode Characters

Handle multi-byte characters correctly:

```gleam
fn calculate_pointer_length(text: String, start: Int, end: Int) -> Int {
  // Count grapheme clusters, not bytes
  text
  |> string.slice(start, end - start)
  |> grapheme_count
}
```

---

## Color Support

### ANSI Color Codes

```gleam
pub type Color {
  Red
  Yellow
  Green
  Blue
  Cyan
  Magenta
  White
}

pub fn colorize(text: String, color: Color) -> String {
  let code = case color {
    Red -> "\x1b[31m"
    Blue -> "\x1b[34m"
    // ...
  }
  code <> text <> "\x1b[0m"
}
```

### Colored Output Example

```
error[E0101]: Type mismatch
   ┌─ src/example.core.tao:3:5
   │
 3 │ let f = (x : $I32) -> x
   │           ──────
   │           │
   │           expected type is $Type
   │
   = note: Function parameter types must be $Type
```

- Error type: **Red**
- File location: **Cyan**
- Primary highlight: **Red** (`^^^^^`)
- Secondary highlight: **Blue** (`─────`)
- Notes: **Yellow**

### No-Color Fallback

Detect terminal support:

```gleam
fn supports_color() -> Bool {
  case os.get_env("NO_COLOR") {
    Ok(_) -> False
    Error(_) -> terminal.is_tty()
  }
}
```

---

## Context Lines

Show surrounding code for context:

```
   │
 2 │ let y = 1
   │     ─
   │     this variable is an I32
 3 │ let f = (x : $I32) -> x
   │              ────
   │
```

```gleam
fn get_relevant_lines(
  snippet: SourceSnippet,
) -> List(#(Int, String)) {
  let all_lines = string.split(snippet.source, "\n")
  let min_line = max(0, snippet.line - snippet.context_lines - 1)
  let max_line = min(
    list.length(all_lines),
    snippet.line + snippet.context_lines
  )
  
  list.range(min_line, max_line)
  |> list.map(fn(i) { #(i, list.at(all_lines, i)) })
}
```

---

## Integration with Error Types

```gleam
pub fn error_to_snippet(error: Error) -> SourceSnippet {
  case error {
    TypeMismatch(expected, got, exp_span, got_span, context) ->
      SourceSnippet(
        file: exp_span.file,
        line: exp_span.start_line,
        column: exp_span.start_col,
        source: read_file(exp_span.file),
        highlights: [
          Highlight(exp_span, Primary, Some("expected " <> type_to_string(expected))),
          Highlight(got_span, Secondary, Some("got " <> type_to_string(got))),
        ],
        context_lines: 2,
      )
    // ... other error types
  }
}
```

---

## Testing

### Golden File Tests

```
-- tests/errors/type_mismatch_01.txt --
error[E0101]: Type mismatch
   ┌─ src/example.core.tao:3:5
   │
 3 │ let f = (x : $I32) -> x
   │           ^^^^^^^
   │
   = expected: $Type
   = got:      $I32
```

```gleam
fn test_type_mismatch_snippet() {
  let error = TypeMismatch(...)
  let snippet = error_to_snippet(error)
  let output = format_snippet(snippet)
  
  assert.equal(
    output,
    read_golden_file("type_mismatch_01.txt"),
  )
}
```

---

## Related Documents

- **[01-overview.md](./01-overview.md)** - Error reporting overview
- **[02-error-types.md](./02-error-types.md)** - Error type specifications
- **[04-cli-integration.md](./04-cli-integration.md)** - CLI integration

---

## Implementation Checklist

- [ ] Create `syntax/source_snippet.gleam` module
- [ ] Implement `SourceSnippet` and `Highlight` types
- [ ] Implement snippet formatting algorithm
- [ ] Add multi-span support
- [ ] Handle edge cases (long lines, unicode)
- [ ] Add ANSI color support
- [ ] Add NO_COLOR detection
- [ ] Create golden file test suite
- [ ] Integrate with error types
- [ ] Test with real error scenarios
