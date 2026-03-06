// ============================================================================
// FORMATTER - Language-Agnostic Pretty Printer Library
// ============================================================================
/// A general-purpose pretty-printing library for formatting ASTs into
/// human-readable source code. Supports both C-style (brace-delimited) and
/// Python-style (indentation-based) languages.
///
/// # Overview
///
/// This library provides:
/// - **Document algebra**: Build formatted output from combinators
/// - **Automatic line breaking**: Wrap lines at configured width
/// - **Configurable indentation**: Support for different indentation styles
/// - **Multiple output styles**: C-style, Python-style, etc.
///
/// # Example
///
/// ```gleam
/// import formatter
///
/// // Build a document
/// let doc = formatter.concat([
///   formatter.text("let"),
///   formatter.space,
///   formatter.text("x"),
///   formatter.text("="),
///   formatter.nest(2, formatter.concat([
///     formatter.line,
///     formatter.text("42"),
///   ])),
/// ])
///
/// // Render to string
/// formatter.render(doc, formatter.c_style_config())
/// ```

import gleam/int
import gleam/list
import gleam/string

// ============================================================================
// TYPES
// ============================================================================

/// A formatted document - can be rendered to a string
pub type Doc {
  /// Plain text
  Text(String)
  /// Concatenation of documents
  Concat(List(Doc))
  /// Line break (becomes space or newline)
  Line
  /// Hard line break (always newline)
  HardLine
  /// Indentation level
  Nest(Int, Doc)
  /// Group that can be broken across lines
  Group(Doc)
  /// Conditional - different doc based on line breaking
  IfBroken(Doc, Doc)
}

/// Formatter configuration for different language styles
pub type Config {
  Config(
    /// Maximum line width before breaking
    max_width: Int,
    /// Indentation width in spaces
    indent_width: Int,
    /// Use spaces for indentation (vs tabs)
    spaces: Bool,
    /// Put opening brace on same line (C-style)
    brace_style: BraceStyle,
    /// Add trailing comma in multi-line lists
    trailing_comma: Bool,
  )
}

/// Brace placement style
pub type BraceStyle {
  /// Same line: `func() {`
  SameLine
  /// Next line: `func()`\n`{`
  NextLine
  /// No braces (Python-style)
  None
}

// ============================================================================
// CONFIGURATION
// ============================================================================

/// Default configuration for C-style languages
pub fn c_style_config() -> Config {
  Config(
    max_width: 80,
    indent_width: 2,
    spaces: True,
    brace_style: SameLine,
    trailing_comma: False,
  )
}

/// Configuration for K&R style (common in C, Java)
pub fn kr_style_config() -> Config {
  Config(
    max_width: 100,
    indent_width: 4,
    spaces: True,
    brace_style: SameLine,
    trailing_comma: False,
  )
}

/// Configuration for Allman style (common in C#, PowerShell)
pub fn allman_style_config() -> Config {
  Config(
    max_width: 100,
    indent_width: 4,
    spaces: True,
    brace_style: NextLine,
    trailing_comma: False,
  )
}

/// Configuration for Python-style languages
pub fn python_style_config() -> Config {
  Config(
    max_width: 88,
    indent_width: 4,
    spaces: True,
    brace_style: None,
    trailing_comma: False,
  )
}

/// Configuration for OCaml-style languages
pub fn ocaml_style_config() -> Config {
  Config(
    max_width: 100,
    indent_width: 2,
    spaces: True,
    brace_style: SameLine,
    trailing_comma: False,
  )
}

// ============================================================================
// BASIC DOCUMENTS
// ============================================================================

/// Create a text document
pub fn text(s: String) -> Doc {
  Text(s)
}

/// Create a space character
pub const space = Text(" ")

/// Create a line break (becomes space or newline based on context)
pub const line = Line

/// Create a hard line break (always newline)
pub const hard_line = HardLine

/// Create an empty document
pub const empty = Text("")

// ============================================================================
// COMBINATORS
// ============================================================================

/// Concatenate a list of documents
pub fn concat(docs: List(Doc)) -> Doc {
  Concat(docs)
}

/// Concatenate two documents
pub fn append(doc1: Doc, doc2: Doc) -> Doc {
  Concat([doc1, doc2])
}

/// Nest a document by increasing indentation
pub fn nest(indent: Int, doc: Doc) -> Doc {
  Nest(indent, doc)
}

/// Create a group that can be broken across lines
pub fn group(doc: Doc) -> Doc {
  Group(doc)
}

/// Document that shows differently when broken vs flat
pub fn if_broken(broken: Doc, flat: Doc) -> Doc {
  IfBroken(broken, flat)
}

// ============================================================================
// SEPARATORS
// ============================================================================

/// Join documents with a separator
pub fn join(sep: Doc, docs: List(Doc)) -> Doc {
  case docs {
    [] -> empty
    [d] -> d
    [d, ..rest] -> append(d, append(sep, join(sep, rest)))
  }
}

/// Join documents with comma and space
pub fn comma_sep(docs: List(Doc)) -> Doc {
  join(append(Text(","), space), docs)
}

/// Join documents with space
pub fn space_sep(docs: List(Doc)) -> Doc {
  join(space, docs)
}

/// Join documents with line breaks
pub fn line_sep(docs: List(Doc)) -> Doc {
  join(line, docs)
}

// ============================================================================
// WRAPPING
// ============================================================================

/// Wrap text at word boundaries to max width
pub fn wrap(max_width: Int, text: String) -> Doc {
  let words = string.split(text, " ")
  concat(wrap_words(max_width, words))
}

fn wrap_words(max_width: Int, words: List(String)) -> List(Doc) {
  case words {
    [] -> []
    [word] -> [Text(word)]
    [word, ..rest] -> {
      let wrapped = wrap_words(max_width, rest)
      [Text(word), line, ..wrapped]
    }
  }
}

// ============================================================================
// BLOCK HELPERS
// ============================================================================

/// Format a block with braces: `{ ... }`
pub fn braces(doc: Doc) -> Doc {
  concat([
    Text("{"),
    nest(2, concat([hard_line, doc])),
    hard_line,
    Text("}"),
  ])
}

/// Format a block with parentheses: `( ... )`
pub fn parens(doc: Doc) -> Doc {
  concat([
    Text("("),
    nest(2, concat([line, doc])),
    line,
    Text(")"),
  ])
}

/// Format a block with brackets: `[ ... ]`
pub fn brackets(doc: Doc) -> Doc {
  concat([
    Text("["),
    nest(2, concat([line, doc])),
    line,
    Text("]"),
  ])
}

/// Format a block with optional braces based on config
pub fn block(doc: Doc, config: Config) -> Doc {
  case config.brace_style {
    SameLine | NextLine -> braces(doc)
    None -> nest(config.indent_width, doc)
  }
}

// ============================================================================
// LIST HELPERS
// ============================================================================

/// Format a list with brackets: `[x, y, z]`
pub fn list(docs: List(Doc)) -> Doc {
  brackets(comma_sep(docs))
}

/// Format a list that breaks across lines
pub fn broken_list(docs: List(Doc)) -> Doc {
  brackets(concat([
    hard_line,
    nest(2, line_sep(docs)),
    concat([hard_line, Text(",")]),
  ]))
}

/// Format a list that can break across lines
pub fn flex_list(docs: List(Doc)) -> Doc {
  group(if_broken(broken_list(docs), list(docs)))
}

// ============================================================================
// RENDERING
// ============================================================================

/// Render a document to a string with the given configuration
pub fn render(doc: Doc, config: Config) -> String {
  let state = RenderState(
    current_width: 0,
    current_indent: 0,
    config: config,
  )
  render_doc(doc, state) |> string.join("")
}

type RenderState {
  RenderState(
    current_width: Int,
    current_indent: Int,
    config: Config,
  )
}

fn render_doc(doc: Doc, state: RenderState) -> List(String) {
  case doc {
    Text(s) -> [s]
    Concat(docs) -> list.flat_map(docs, fn(d) { render_doc(d, state) })
    Line ->
      case fits(state.current_width, doc, state) {
        True -> [" "]
        False -> ["\n" <> indent_string(state.current_indent + state.config.indent_width, state.config)]
      }
    HardLine -> ["\n" <> indent_string(state.current_indent + state.config.indent_width, state.config)]
    Nest(indent, inner) ->
      render_doc(inner, RenderState(..state, current_indent: state.current_indent + indent))
    Group(inner) -> render_doc(inner, state)
    IfBroken(broken, flat) ->
      case fits(state.current_width, broken, state) {
        True -> render_doc(flat, state)
        False -> render_doc(broken, state)
      }
  }
}

fn fits(width: Int, doc: Doc, state: RenderState) -> Bool {
  case doc {
    Text(s) -> width + string.length(s) <= state.config.max_width
    Concat(docs) -> fits_list(width, docs, state)
    Line | HardLine -> True
    Nest(_, inner) -> fits(width, inner, state)
    Group(inner) -> fits(width, inner, state)
    IfBroken(_, flat) -> fits(width, flat, state)
  }
}

fn fits_list(width: Int, docs: List(Doc), state: RenderState) -> Bool {
  case docs {
    [] -> True
    [d, ..rest] ->
      case fits(width, d, state) {
        True -> fits_list(width, rest, state)
        False -> False
      }
  }
}

fn indent_string(indent: Int, config: Config) -> String {
  let ch = case config.spaces {
    True -> " "
    False -> "\t"
  }
  string.repeat(ch, indent)
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Convert a value to a document
pub fn from_string(s: String) -> Doc {
  Text(s)
}

/// Convert an integer to a document
pub fn from_int(i: Int) -> Doc {
  Text(int.to_string(i))
}

/// Convert a list of values to documents
pub fn from_list(items: List(a), f: fn(a) -> Doc) -> Doc {
  list(items |> list.map(f))
}

/// Add a trailing comma if configured
pub fn trailing(doc: Doc, config: Config) -> Doc {
  case config.trailing_comma {
    True -> append(doc, Text(","))
    False -> doc
  }
}

/// Surround a document with whitespace
pub fn surround(left: Doc, doc: Doc, right: Doc) -> Doc {
  concat([left, doc, right])
}

/// Add parentheses around a document
pub fn parenthesize(doc: Doc) -> Doc {
  surround(Text("("), doc, Text(")"))
}
