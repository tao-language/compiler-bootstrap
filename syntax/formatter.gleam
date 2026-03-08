// ============================================================================
// FORMATTER - Document Algebra Pretty Printer
// ============================================================================
/// A pretty printing library with:
/// - Document algebra (Text, Line, Group, Nest, Concat)
/// - Automatic line breaking at configured width
/// - Configurable indentation
///
/// # Example
///
/// ```gleam
/// import formatter
///
/// let doc = formatter.concat([
///   formatter.text("let "),
///   formatter.text("x"),
///   formatter.text(" = "),
///   formatter.text("42"),
/// ])
///
/// formatter.render(doc, 80)
/// ```
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
  /// Soft line break (space or newline depending on group)
  Line
  /// Hard line break (always newline)
  HardLine
  /// Group (try flat, expand if doesn't fit)
  Group(Doc)
  /// Nest (increase indentation by n spaces)
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

/// Soft line break (becomes space or newline)
pub fn line() -> Doc {
  Line
}

/// Hard line break (always newline)
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
    _ -> Concat(flatten_docs(docs))
  }
}

fn flatten_docs(docs: List(Doc)) -> List(Doc) {
  list.flat_map(docs, fn(d) {
    case d {
      Concat(inner) -> inner
      Empty -> []
      _ -> [d]
    }
  })
}

/// Concatenate two documents
pub fn append(d1: Doc, d2: Doc) -> Doc {
  concat([d1, d2])
}

/// Increase indentation
pub fn nest(n: Int, doc: Doc) -> Doc {
  case n <= 0 {
    True -> doc
    False -> Nest(n, doc)
  }
}

/// Group for line breaking (try flat first)
pub fn group(doc: Doc) -> Doc {
  Group(doc)
}

/// Join documents with separator
pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [first] -> first
    [first, ..rest] -> {
      concat(list.fold(right: rest, left: first, fn(acc, d) {
        concat([acc, sep, d])
      }))
    }
  }
}

/// Comma-separated list
pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(concat([text(","), line()]), docs)
}

/// Space-separated list
pub fn space_sep(docs: List(Doc)) -> Doc {
  join(space(), docs)
}

/// Line-separated list
pub fn line_sep(docs: List(Doc)) -> Doc {
  join(hardline(), docs)
}

// ============================================================================
// BLOCK HELPERS
// ============================================================================

/// Wrap in braces with formatting
pub fn braces(doc: Doc) -> Doc {
  concat([text("{"), doc, text("}")])
}

/// Wrap in parentheses
pub fn parens(doc: Doc) -> Doc {
  concat([text("("), doc, text(")")])
}

/// Wrap in brackets
pub fn brackets(doc: Doc) -> Doc {
  concat([text("["), doc, text("]")])
}

/// Block with opening/closing delimiters
pub fn block(
  open: String,
  children: List(Doc),
  close: String,
  indent: Int,
) -> Doc {
  case children {
    [] -> text(open <> close)
    [first] -> {
      concat([
        text(open),
        first,
        text(close),
      ])
    }
    _ -> {
      group(concat([
        text(open),
        nest(indent, concat([
          hardline(),
          join(concat([text(","), hardline()]), children),
        ])),
        hardline(),
        text(close),
      ]))
    }
  }
}

// ============================================================================
// BINARY OPERATOR FORMATTING
// ============================================================================

import syntax/grammar.{type LayoutStyle}

/// Format binary operator with layout support
pub fn format_binop(
  left: Doc,
  right: Doc,
  separator: String,
  precedence: Int,
  parent_prec: Int,
  layout: LayoutStyle,
) -> Doc {
  let inner = case layout {
    Inline -> {
      concat([
        left,
        text(separator),
        right,
      ])
    }
    BreakAfterOperator(indent) -> {
      group(concat([
        left,
        text(separator),
        line(),
        nest(indent, right),
      ]))
    }
    BreakBeforeOperator(indent) -> {
      group(concat([
        left,
        line(),
        nest(indent, concat([
          text(separator),
          right,
        ])),
      ]))
    }
    Block(open, close, indent) -> {
      group(concat([
        text(open),
        nest(indent, concat([
          hardline(),
          left,
          text(separator),
          hardline(),
          right,
        ])),
        text(close),
      ]))
    }
  }

  wrap_parens(inner, precedence < parent_prec)
}

/// Wrap in parens if condition is true
pub fn wrap_parens(doc: Doc, condition: Bool) -> Doc {
  case condition {
    True -> concat([text("("), doc, text(")")])
    False -> doc
  }
}

// ============================================================================
// RENDERING
// ============================================================================

/// Render document to string with default width (80)
pub fn render_default(doc: Doc) -> String {
  render(doc, 80)
}

/// Render document to string with specified width
pub fn render(doc: Doc, width: Int) -> String {
  let formatted = format_to_string(doc, width, 0, True)
  string.trim(formatted)
}

type FormatState =
  #(Int, Bool) // (remaining width, flat mode)

fn format_to_string(
  doc: Doc,
  width: Int,
  indent: Int,
  flat: Bool,
) -> String {
  case doc {
    Empty -> ""
    Text(s) -> s
    Line -> {
      case flat {
        True -> " "
        False -> "\n" <> string.repeat(" ", indent)
      }
    }
    HardLine -> "\n" <> string.repeat(" ", indent)
    Group(inner) => {
      // Try flat first
      let flat_str = format_to_string(inner, width, indent, True)
      case fits(flat_str, width) {
        True -> flat_str
        False -> format_to_string(inner, width, indent, False)
      }
    }
    Nest(n, inner) -> format_to_string(inner, width, indent + n, flat)
    Concat(docs) -> {
      string.concat(list.map(docs, fn(d) {
        format_to_string(d, width, indent, flat)
      }))
    }
  }
}

fn fits(s: String, width: Int) -> Bool {
  // Check if string fits on one line (no newlines and within width)
  case string.contains(s, "\n") {
    True -> False
    False -> {
      let lines = string.split(s, "\n")
      case lines {
        [first] -> string.length(first) <= width
        _ -> False
      }
    }
  }
}

// ============================================================================
// UTILITIES
// ============================================================================

/// Convert string to document
pub fn from_string(s: String) -> Doc {
  text(s)
}

/// Convert int to document
pub fn from_int(n: Int) -> Doc {
  text(int_to_string(n))
}

fn int_to_string(n: Int) -> String {
  n |> int.to_string
}

/// Convert float to document
pub fn from_float(f: Float) -> Doc {
  text(float_to_string(f))
}

fn float_to_string(f: Float) -> String {
  f |> float.to_string
}

/// Indent by n spaces
pub fn indent(n: Int, doc: Doc) -> Doc {
  nest(n, doc)
}

/// Surround document with left and right
pub fn surround(left: Doc, doc: Doc, right: Doc) -> Doc {
  concat([left, doc, right])
}
