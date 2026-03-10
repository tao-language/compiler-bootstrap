// ============================================================================
// SOURCE SNIPPET FORMATTER
// ============================================================================
/// Pretty-print source code with error highlights.
///
/// Produces output like:
/// ```
/// error[E0101]: Type mismatch
///    ┌─ src/file.core.tao:3:5
///    │
///  3 │ (x : $I32) -> x
///    │     ^^^^^
///    │
///    = expected: $Type
///    = got:      $I32
/// ```
import gleam/int
import gleam/list
import gleam/option.{type Option}
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

pub type Span {
  Span(
    file: String,
    start_line: Int,    // 1-based
    start_col: Int,     // 1-based
    end_line: Int,      // 1-based
    end_col: Int,       // 1-based
  )
}

pub type HighlightStyle {
  Primary
  Secondary
}

pub type Highlight {
  Highlight(span: Span, style: HighlightStyle, label: Option(String))
}

pub type Diagnostic {
  Diagnostic(
    code: String,           // e.g., "E0101"
    severity: Severity,
    message: String,
    primary_span: Span,
    spans: List(Highlight),
    notes: List(String),
    hints: List(String),
  )
}

pub type Severity {
  Error
  Warning
  Info
}

// ============================================================================
// FORMATTING
// ============================================================================

pub fn format_diagnostic(diagnostic: Diagnostic, source: String) -> String {
  let header = format_header(diagnostic)
  let snippet = format_snippet(diagnostic, source)
  let footer = format_footer(diagnostic)
  
  string.join([header, snippet, footer], "\n")
}

fn format_header(diagnostic: Diagnostic) -> String {
  let severity_str = case diagnostic.severity {
    Error -> "error"
    Warning -> "warning"
    Info -> "info"
  }
  
  severity_str <> "[" <> diagnostic.code <> "]: " <> diagnostic.message
}

fn format_snippet(diagnostic: Diagnostic, source: String) -> String {
  let lines = string.split(source, "\n")
  let primary = diagnostic.primary_span
  
  // Calculate which lines to show (context around the error)
  let context_lines = 2
  let min_line = int.max(0, primary.start_line - context_lines - 1)
  let max_line = int.min(list.length(lines), primary.end_line + context_lines)
  
  // Find the max line number width for alignment
  let max_line_num = int.to_string(max_line) |> string.length
  
  // Build the snippet
  let top_border = format_top_border(primary, max_line_num)
  let line_docs = format_lines(lines, min_line, max_line, diagnostic, max_line_num)
  
  string.join([top_border, line_docs] |> list.append(format_bottom_border()), "\n")
}

fn format_top_border(span: Span, line_num_width: Int) -> String {
  let padding = string.repeat(" ", line_num_width + 1)
  padding <> "┌─ " <> span.file <> ":" <> int.to_string(span.start_line) <> ":" <> int.to_string(span.start_col)
}

fn format_bottom_border() -> List(String) {
  []
}

fn format_lines(
  lines: List(String),
  start: Int,
  end: Int,
  diagnostic: Diagnostic,
  line_num_width: Int,
) -> String {
  let line_range = list.range(start, end - 1)
  
  line_range
  |> list.map(fn(line_idx) {
    let line_num = line_idx + 1
    let line_content = get_line(lines, line_idx)
    
    let formatted_line = format_single_line(
      line_num,
      line_content,
      diagnostic,
      line_num_width,
    )
    
    formatted_line
  })
  |> string.join("\n")
}

fn get_line(lines: List(String), idx: Int) -> String {
  case list.drop(lines, idx) {
    [line, ..] -> line
    [] -> ""
  }
}

fn format_single_line(
  line_num: Int,
  line_content: String,
  diagnostic: Diagnostic,
  line_num_width: Int,
) -> String {
  let line_num_str = int.to_string(line_num)
  let padding = string.repeat(" ", line_num_width - string.length(line_num_str))
  let line_prefix = padding <> line_num_str <> " │ "
  
  // Check if this line has any highlights
  let highlights = get_highlights_for_line(diagnostic.spans, line_num, diagnostic.primary_span)
  
  case highlights {
    [] -> {
      // No highlights, just show the line with a margin bar
      line_prefix <> line_content
    }
    hs -> {
      // Has highlights, show line and pointer
      let pointer_line = build_pointer_line(hs, line_content, line_prefix)
      line_prefix <> line_content <> "\n" <> pointer_line
    }
  }
}

fn get_highlights_for_line(
  spans: List(Highlight),
  line_num: Int,
  primary_span: Span,
) -> List(#(Int, Int, HighlightStyle)) {
  // Get all highlights that affect this line
  let primary_highlights = case primary_span.start_line == line_num || primary_span.end_line == line_num {
    True -> [#(primary_span.start_col, primary_span.end_col, Primary)]
    False -> []
  }
  
  let secondary_highlights = spans
  |> list.filter(fn(h) { h.span.start_line <= line_num && h.span.end_line >= line_num })
  |> list.map(fn(h) { #(h.span.start_col, h.span.end_col, h.style) })
  
  list.append(primary_highlights, secondary_highlights)
}

fn build_pointer_line(
  highlights: List(#(Int, Int, HighlightStyle)),
  line_content: String,
  line_prefix: String,
) -> String {
  let pointer_base = string.repeat(" ", string.length(line_prefix))
  
  let pointers = highlights
  |> list.map(fn(h) {
    let #(start, end, style) = h
    let pointer_char = case style {
      Primary -> "^"
      Secondary -> "-"
    }
    
    let pointer_length = int.max(1, end - start)
    string.repeat(pointer_char, pointer_length)
  })
  |> list.intersperse(string.repeat(" ", 1))
  |> string.join("")
  
  // Pad the pointer to align with the highlight
  let first_highlight = list.first(highlights)
  case first_highlight {
    Ok(h) -> {
      let #(start, _, _) = h
      let padding = string.repeat(" ", start - 1)
      pointer_base <> padding <> pointers
    }
    _ -> pointer_base
  }
}

fn format_footer(diagnostic: Diagnostic) -> String {
  let notes = diagnostic.notes
  |> list.map(fn(note) { "  = note: " <> note })
  
  let hints = diagnostic.hints
  |> list.map(fn(hint) { "  = hint: " <> hint })
  
  let footer_items = list.append(notes, hints)
  
  case footer_items {
    [] -> ""
    [..] -> string.join(footer_items, "\n")
  }
}

// ============================================================================
// HELPERS
// ============================================================================

pub fn span_from_positions(
  file: String,
  start_line: Int,
  start_col: Int,
  end_line: Int,
  end_col: Int,
) -> Span {
  Span(file, start_line, start_col, end_line, end_col)
}

pub fn merge_spans(span1: Span, span2: Span) -> Span {
  Span(
    span1.file,
    int.min(span1.start_line, span2.start_line),
    int.min(span1.start_col, span2.start_col),
    int.max(span1.end_line, span2.end_line),
    int.max(span1.end_col, span2.end_col),
  )
}
