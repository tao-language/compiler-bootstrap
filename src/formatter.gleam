// ============================================================================
// FORMATTER - Simple Pretty Printer
// ============================================================================

/// A simple pretty printing library with:
/// - Simple document algebra
/// - Automatic line breaking
/// - Configurable indentation
///
/// # Example
///
/// ```gleam
/// import formatter
///
/// // Create a document
/// let doc = formatter.concat([
///   formatter.text("let "),
///   formatter.text("x"),
///   formatter.text(" = "),
///   formatter.text("42"),
/// ])
///
/// // Render at 80 characters width
/// let output = formatter.render(doc, 80)
/// ```
import gleam/float
import gleam/int
import gleam/list
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// Document type for formatting
pub type Doc {
  /// Empty document
  Empty
  /// Plain text (no line breaks)
  Text(String)
  /// Soft line break (space or newline)
  Line
  /// Hard line break (always newline)
  HardLine
  /// Group (try flat, expand if needed)
  Group(Doc)
  /// Nest (increase indentation)
  Nest(Int, Doc)
  /// Concatenate documents
  Concat(List(Doc))
}

// ============================================================================
// BASIC CONSTRUCTORS
// ============================================================================

/// Empty document
pub fn empty() -> Doc {
  Empty
}

/// Text document
pub fn text(s: String) -> Doc {
  case s == "" {
    True -> Empty
    False -> Text(s)
  }
}

/// Space character
pub fn space() -> Doc {
  text(" ")
}

/// Soft line break
pub fn line() -> Doc {
  Line
}

/// Hard line break
pub fn hardline() -> Doc {
  HardLine
}

// ============================================================================
// COMBINATORS
// ============================================================================

/// Concatenate documents
pub fn concat(docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    _ -> Concat(docs)
  }
}

/// Concatenate two documents
pub fn append(d1: Doc, d2: Doc) -> Doc {
  concat([d1, d2])
}

/// Group for potential line breaking
pub fn group(doc: Doc) -> Doc {
  case doc {
    Empty -> Empty
    _ -> Group(doc)
  }
}

/// Increase indentation
pub fn nest(indent: Int, doc: Doc) -> Doc {
  case doc {
    Empty -> Empty
    _ -> Nest(indent, doc)
  }
}

/// Join documents with separator
pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    [d, ..rest] -> concat([d, sep, join(sep, rest)])
  }
}

// ============================================================================
// CONVENIENCE COMBINATORS
// ============================================================================

/// Space-separated list
pub fn hsep(docs: List(Doc)) -> Doc {
  join(space(), docs)
}

/// Vertical separation (hard line breaks)
pub fn vsep(docs: List(Doc)) -> Doc {
  join(hardline(), docs)
}

/// Comma-separated list
pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(concat([text(","), line()]), docs)
}

/// Parentheses
pub fn parens(doc: Doc) -> Doc {
  concat([text("("), doc, text(")")])
}

/// Braces
pub fn braces(doc: Doc) -> Doc {
  concat([text("{"), line(), nest(2, doc), line(), text("}")])
}

/// Brackets
pub fn brackets(doc: Doc) -> Doc {
  concat([text("["), doc, text("]")])
}

/// Block with braces
pub fn block(content: Doc) -> Doc {
  case content {
    Empty -> text("{}")
    _ -> braces(content)
  }
}

/// Keyword followed by space
pub fn kw(s: String) -> Doc {
  concat([text(s), space()])
}

/// Optional semicolon
pub fn opt_semi(present: Bool) -> Doc {
  case present {
    True -> text(";")
    False -> Empty
  }
}

// ============================================================================
// RENDERING
// ============================================================================

/// Render document to string
pub fn render(doc: Doc, width: Int) -> String {
  render_doc(doc, width, 0, True)
}

/// Render with default width (80)
pub fn render_default(doc: Doc) -> String {
  render(doc, 80)
}

fn render_doc(doc: Doc, width: Int, col: Int, is_flat: Bool) -> String {
  case doc {
    Empty -> ""
    Text(s) -> s
    Line ->
      case is_flat {
        True -> " "
        False -> "\n" <> string.repeat(" ", col)
      }
    HardLine -> "\n" <> string.repeat(" ", col)
    Group(inner) -> {
      // Try flat first
      let flat = render_doc(inner, width, col, True)
      case string.length(flat) + col <= width {
        True -> flat
        False -> render_doc(inner, width, col, False)
      }
    }
    Nest(indent, inner) -> render_doc(inner, width, col + indent, is_flat)
    Concat(docs) -> {
      list.fold(docs, "", fn(acc, d) {
        acc <> render_doc(d, width, col + string.length(acc), is_flat)
      })
    }
  }
}

// ============================================================================
// EXPRESSION FORMATTING
// ============================================================================

/// Format expression with precedence-aware parentheses
pub fn format_expr(
  doc: Doc,
  expr_prec: Int,
  parent_prec: Int,
  assoc: Assoc,
) -> Doc {
  let needs_parens = case assoc {
    Left -> expr_prec < parent_prec
    Right -> expr_prec < parent_prec
    NonAssoc -> expr_prec <= parent_prec
  }
  case needs_parens {
    True -> parens(doc)
    False -> doc
  }
}

/// Associativity
pub type Assoc {
  Left
  Right
  NonAssoc
}

/// Get associativity from string
pub fn assoc_from_string(s: String) -> Assoc {
  case string.lowercase(s) {
    "left" | "l" -> Left
    "right" | "r" -> Right
    _ -> NonAssoc
  }
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Convert int to document
pub fn int_doc(i: Int) -> Doc {
  text(int.to_string(i))
}

/// Convert float to document
pub fn float_doc(f: Float) -> Doc {
  text(float.to_string(f))
}

/// Quoted string
pub fn quoted_string(s: String) -> Doc {
  concat([text("\""), text(s), text("\"")])
}

/// Check if document is empty
pub fn is_empty(doc: Doc) -> Bool {
  case doc {
    Empty -> True
    _ -> False
  }
}

/// Get document width (approximate)
pub fn width(doc: Doc) -> Int {
  case doc {
    Empty -> 0
    Text(s) -> string.length(s)
    Line -> 1
    HardLine -> 0
    Group(d) -> width(d)
    Nest(_, d) -> width(d)
    Concat(docs) -> list.fold(docs, 0, fn(acc, d) { acc + width(d) })
  }
}
