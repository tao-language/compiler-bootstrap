// ============================================================================
// FORMATTER - Pretty Printing with Layout Algebra
// ============================================================================
/// A pretty printing library based on Wadler's "A Prettier Printer" paper.
///
/// This library provides:
/// - Layout algebra for composable document formatting
/// - Automatic line breaking based on width
/// - Configurable indentation
/// - Precedence-aware expression formatting
///
/// # Example
///
/// ```gleam
/// import formatter.{type Doc, text, line, group, nest, concat}
///
/// // Create a document
/// let doc = group(
///   concat(
///     text("let"),
///     concat(
///       line(),
///       nest(2, concat(text("x"), concat(line(), text("= 42"))))
///     )
///   )
/// )
///
/// // Render with 80 character width
/// let output = formatter.render(doc, 80, "  ")
/// ```

import gleam/int
import gleam/list
import gleam/float
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// Layout document - can be rendered at different widths
pub type Doc {
  /// Empty document
  Empty
  /// Text segment (cannot be broken)
  Text(String)
  /// Line break (becomes space or newline depending on layout)
  Line
  /// Forced line break (always newline)
  HardLine
  /// Nested/indented document
  Nest(Int, Doc)
  /// Choice between compact and expanded layout
  FlatAlt(Doc, Doc)
  /// Group: try flat first, expand if doesn't fit
  Group(Doc)
  /// Concatenate documents
  Concat(Doc, Doc)
}

/// Formatting context
pub type FormatContext {
  FormatContext(
    /// Current line width limit
    width: Int,
    /// Current indentation string
    indent: String,
    /// Current column position
    col: Int,
    /// Whether we're in "flat" mode (trying to fit on one line)
    is_flat: Bool,
  )
}

/// Associativity for expression formatting
pub type Assoc {
  Left
  Right
  NonAssoc
}

// ============================================================================
// BASIC DOCUMENT CONSTRUCTORS
// ============================================================================

/// Empty document
pub fn empty() -> Doc {
  Empty
}

/// Text (cannot be broken)
pub fn text(str: String) -> Doc {
  case str == "" {
    True -> Empty
    False -> Text(str)
  }
}

/// Line break (space or newline)
pub fn line() -> Doc {
  Line
}

/// Hard line break (always newline)
pub fn hardline() -> Doc {
  HardLine
}

/// Space character
pub fn space() -> Doc {
  text(" ")
}

/// Comma followed by optional line break
pub fn comma() -> Doc {
  concat(text(","), line())
}

/// Semicolon followed by optional line break
pub fn semi() -> Doc {
  concat(text(";"), line())
}

// ============================================================================
// DOCUMENT COMBINATORS
// ============================================================================

/// Concatenate documents
pub fn concat(doc1: Doc, doc2: Doc) -> Doc {
  case doc1, doc2 {
    Empty, _ -> doc2
    _, Empty -> doc1
    _, _ -> Concat(doc1, doc2)
  }
}

/// Concatenate list of documents
pub fn concat_all(docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    [d, ..ds] -> concat(d, concat_all(ds))
  }
}

/// Join documents with separator
pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> Empty
    [d] -> d
    [d, ..ds] -> concat(d, concat_all(list.map(ds, fn(x) { concat(sep, x) })))
  }
}

/// Nest document by indentation
pub fn nest(indent: Int, doc: Doc) -> Doc {
  case doc {
    Empty -> Empty
    _ -> Nest(indent, doc)
  }
}

/// Group: try flat first, expand if doesn't fit
pub fn group(doc: Doc) -> Doc {
  case doc {
    Empty -> Empty
    _ -> Group(doc)
  }
}

/// Flat alternative: use first if fits, otherwise second
pub fn flat_alt(flat: Doc, expanded: Doc) -> Doc {
  case flat {
    Empty -> Empty
    _ -> FlatAlt(flat, expanded)
  }
}

// ============================================================================
// FORMATTING COMBINATORS
// ============================================================================

/// Format with parentheses if needed
pub fn parens_if(cond: Bool, doc: Doc) -> Doc {
  case cond {
    True -> parens(doc)
    False -> doc
  }
}

/// Format block with braces
pub fn braces(doc: Doc) -> Doc {
  concat(text("{"), concat(doc, text("}")))
}

/// Format block with braces and space
pub fn braces_space(doc: Doc) -> Doc {
  concat(text("{ "), concat(doc, text(" }")))
}

/// Format block with parens
pub fn parens(doc: Doc) -> Doc {
  concat(text("("), concat(doc, text(")")))
}

/// Format block with brackets
pub fn brackets(doc: Doc) -> Doc {
  concat(text("["), concat(doc, text("]")))
}

/// Format angle brackets
pub fn angles(doc: Doc) -> Doc {
  concat(text("<"), concat(doc, text(">")))
}

/// Format comma-separated list
pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(comma(), docs)
}

/// Format space-separated list
pub fn space_sep(docs: List(Doc)) -> Doc {
  join(space(), docs)
}

/// Format list with soft line breaks
pub fn soft_sep(docs: List(Doc)) -> Doc {
  join(concat(line(), text(" ")), docs)
}

/// Format indented block
pub fn indented(doc: Doc) -> Doc {
  nest(2, doc)
}

/// Format hanging indent (first line flush, rest indented)
pub fn hanging_indent(indent: Int, doc: Doc) -> Doc {
  nest(indent, doc)
}

/// Format optional semicolon
pub fn opt_semi(cond: Bool) -> Doc {
  case cond {
    True -> semi()
    False -> Empty
  }
}

/// Fill: like concat but with space between non-empty elements
pub fn fill(doc1: Doc, doc2: Doc) -> Doc {
  case doc1, doc2 {
    Empty, _ -> doc2
    _, Empty -> doc1
    _, _ -> concat(doc1, concat(space(), doc2))
  }
}

// ============================================================================
// RENDERING
// ============================================================================

/// Render document to string
pub fn render(doc: Doc, width: Int, indent: String) -> String {
  let initial_context = FormatContext(
    width: width,
    indent: indent,
    col: 0,
    is_flat: True,
  )
  render_best(width, indent, [#(0, doc)])
}

/// Default render with 80 character width and 2-space indent
pub fn render_default(doc: Doc) -> String {
  render(doc, 80, "  ")
}

/// Best-fit rendering algorithm
fn render_best(width: Int, indent: String, docs: List(#(Int, Doc))) -> String {
  case docs {
    [] -> ""
    [#(n, doc), ..rest] ->
      case doc {
        Empty -> render_best(width, indent, rest)
        Text(s) -> s <> render_best(width, indent, advance(n, string.length(s), rest))
        Line -> " " <> render_best(width, indent, rest)
        HardLine -> "\n" <> string.repeat(indent, n) <> render_best(width, indent, rest)
        Nest(i, d) -> render_best(width, indent, [#(n + i, d), ..rest])
        FlatAlt(flat, _) -> render_best(width, indent, [#(n, flat), ..rest])
        Group(d) -> {
          let flat = flatten(d)
          case fits(width, n, [#(0, flat)]) {
            True -> render_best(width, indent, [#(n, flat), ..rest])
            False -> render_best(width, indent, [#(n, d), ..rest])
          }
        }
        Concat(d1, d2) -> render_best(width, indent, [#(n, d1), #(n, d2), ..rest])
      }
  }
}

/// Advance column position
fn advance(n: Int, len: Int, docs: List(#(Int, Doc))) -> List(#(Int, Doc)) {
  case docs {
    [] -> []
    [#(m, d), ..rest] -> [#(m, d), ..advance(n, len, rest)]
  }
}

/// Check if document fits within width
fn fits(width: Int, col: Int, docs: List(#(Int, Doc))) -> Bool {
  case col > width {
    True -> False
    False ->
      case docs {
        [] -> True
        [#(_, doc), ..rest] ->
          case doc {
            Empty -> fits(width, col, rest)
            Text(s) -> fits(width, col + string.length(s), rest)
            Line -> True
            HardLine -> True
            Nest(_, d) -> fits(width, col, [#(0, d), ..rest])
            FlatAlt(flat, _) -> fits(width, col, [#(0, flat), ..rest])
            Group(d) -> fits(width, col, [#(0, flatten(d)), ..rest])
            Concat(d1, d2) -> fits(width, col, [#(0, d1), #(0, d2), ..rest])
          }
      }
  }
}

/// Flatten document for single-line rendering
pub fn flatten(doc: Doc) -> Doc {
  case doc {
    Empty -> Empty
    Text(s) -> Text(s)
    Line -> text(" ")
    HardLine -> text(" ")
    Nest(i, d) -> Nest(i, flatten(d))
    FlatAlt(flat, _) -> flatten(flat)
    Group(d) -> Group(flatten(d))
    Concat(d1, d2) -> concat(flatten(d1), flatten(d2))
  }
}

// ============================================================================
// PRECEDENCE-AWARE EXPRESSION FORMATTING
// ============================================================================

/// Format expression with precedence-aware parentheses
pub fn format_expr(
  expr_doc: Doc,
  expr_prec: Int,
  parent_prec: Int,
  assoc: Assoc,
) -> Doc {
  let needs_parens = case assoc {
    Left -> expr_prec < parent_prec
    Right -> expr_prec < parent_prec
    NonAssoc -> expr_prec <= parent_prec
  }
  parens_if(needs_parens, expr_doc)
}

/// Get associativity from string
pub fn assoc_from_string(s: String) -> Assoc {
  case s {
    "left" | "Left" | "l" -> Left
    "right" | "Right" | "r" -> Right
    _ -> NonAssoc
  }
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Check if document is multi-line
pub fn is_multi_line(doc: Doc) -> Bool {
  case doc {
    Empty -> False
    Text(_) -> False
    Line -> True
    HardLine -> True
    Nest(_, d) -> is_multi_line(d)
    FlatAlt(_, _) -> False
    Group(d) -> is_multi_line(d)
    Concat(d1, d2) -> is_multi_line(d1) || is_multi_line(d2)
  }
}

/// Check if document is single-line
pub fn is_single_line(doc: Doc) -> Bool {
  !is_multi_line(doc)
}

/// Create a simple text document
pub fn str(s: String) -> Doc {
  text(s)
}

/// Create a document from int
pub fn int(i: Int) -> Doc {
  text(int.to_string(i))
}

/// Create a document from float
pub fn float_doc(f: Float) -> Doc {
  text(float.to_string(f))
}

/// Wrap document in quotes
pub fn quoted(doc: Doc) -> Doc {
  concat(text("\""), concat(doc, text("\"")))
}

/// Wrap string in quotes
pub fn quoted_string(s: String) -> Doc {
  quoted(text(s))
}

/// Create a block with opening and closing delimiters
pub fn block(open: Doc, close: Doc, content: Doc) -> Doc {
  group(
    concat(
      open,
      concat(
        nest(2, concat(hardline(), content)),
        concat(hardline(), close)
      )
    )
  )
}

/// Create a block with braces
pub fn brace_block(content: Doc) -> Doc {
  block(text("{"), text("}"), content)
}

/// Create a block with parens
pub fn paren_block(content: Doc) -> Doc {
  block(text("("), text(")"), content)
}

/// Create a block with brackets
pub fn bracket_block(content: Doc) -> Doc {
  block(text("["), text("]"), content)
}

/// Horizontal concatenation (alias for concat)
pub fn hcat(docs: List(Doc)) -> Doc {
  concat_all(docs)
}

/// Vertical concatenation
pub fn vcat(docs: List(Doc)) -> Doc {
  join(hardline(), docs)
}

/// Fill concatenation (like hcat but with spaces)
pub fn hsep(docs: List(Doc)) -> Doc {
  join(space(), docs)
}

/// Vertical fill (with line breaks)
pub fn vsep(docs: List(Doc)) -> Doc {
  join(line(), docs)
}

/// Create a document that is either flat or expanded
pub fn enclose_sep(
  open: Doc,
  close: Doc,
  sep: Doc,
  docs: List(Doc),
) -> Doc {
  case docs {
    [] -> concat(open, close)
    _ ->
      group(
        concat(
          open,
          concat(
            nest(2, concat(line(), join(sep, docs))),
            concat(line(), close)
          )
        )
      )
  }
}

/// Comma-separated list in brackets
pub fn brackets_list(docs: List(Doc)) -> Doc {
  enclose_sep(text("["), text("]"), comma(), docs)
}

/// Comma-separated list in braces
pub fn braces_list(docs: List(Doc)) -> Doc {
  enclose_sep(text("{"), text("}"), comma(), docs)
}

/// Comma-separated list in parens
pub fn parens_list(docs: List(Doc)) -> Doc {
  enclose_sep(text("("), text(")"), comma(), docs)
}
