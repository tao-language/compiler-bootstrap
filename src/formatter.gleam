// ============================================================================
// FORMATTER - Grammar-Based Tree Formatter
// ============================================================================

/// A formatter that walks a parse tree using grammar structure to produce
/// properly formatted output with indentation and layout.
import gleam/list
import gleam/string
import parser

// ============================================================================
// TYPES
// ============================================================================

/// Formatting context
pub type FormatContext {
  FormatContext(
    /// Current indentation level
    indent: Int,
    /// Indentation string (e.g., "  " for 2 spaces)
    indent_string: String,
  )
}

/// A formatter function
pub type Formatter {
  Formatter(format: fn(parser.ParseTree, FormatContext) -> String)
}

// ============================================================================
// CONTEXT HELPERS
// ============================================================================

/// Create a new format context
pub fn new_context() -> FormatContext {
  FormatContext(0, "  ")
}

/// Create context with custom indent
pub fn with_indent(indent_string: String) -> FormatContext {
  FormatContext(0, indent_string)
}

/// Increase indentation level
pub fn indent(ctx: FormatContext) -> FormatContext {
  FormatContext(ctx.indent + 1, ctx.indent_string)
}

/// Get current indentation string
fn get_indent(ctx: FormatContext) -> String {
  string.repeat(ctx.indent_string, ctx.indent)
}

// ============================================================================
// BASIC FORMATTERS
// ============================================================================

/// Format a token (leaf node)
pub fn format_token(tree: parser.ParseTree, _ctx: FormatContext) -> String {
  case tree {
    parser.TreeToken(value) -> value
    parser.TreeNode(_, _) -> ""
  }
}

/// Format a node with children on same line
pub fn format_inline(tree: parser.ParseTree, ctx: FormatContext) -> String {
  case tree {
    parser.TreeToken(value) -> value
    parser.TreeNode(_, children) ->
      children
      |> list.map(fn(c) { format_inline(c, ctx) })
      |> string.join(" ")
  }
}

/// Format a node with children on separate lines (indented)
pub fn format_block(tree: parser.ParseTree, ctx: FormatContext) -> String {
  let indented_ctx = indent(ctx)
  case tree {
    parser.TreeToken(value) -> value
    parser.TreeNode(_, children) ->
      children
      |> list.map(fn(c) { format_block(c, indented_ctx) })
      |> string.join("\n")
  }
}

// ============================================================================
// GRAMMAR-BASED FORMATTER
// ============================================================================

/// Format a parse tree using grammar-aware formatting
pub fn format(tree: parser.ParseTree) -> String {
  format_with_context(tree, new_context())
}

/// Format with custom context
pub fn format_with_context(tree: parser.ParseTree, ctx: FormatContext) -> String {
  format_node(tree, ctx)
}

fn format_node(tree: parser.ParseTree, ctx: FormatContext) -> String {
  case tree {
    parser.TreeToken(value) -> value
    parser.TreeNode(name, children) -> format_by_name(name, children, ctx)
  }
}

fn format_by_name(
  name: String,
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  let tree = parser.TreeNode(name, children)
  case name {
    // Lambda: \x. body
    "Term" ->
      case children {
        [token, body] if token == parser.TreeToken("\\") ->
          format_lambda(children, ctx)
        _ -> format_inline(tree, ctx)
      }

    // Let binding: let x = expr
    "Start" ->
      case children {
        [let_token, _, eq_token, expr]
          if let_token == parser.TreeToken("let")
          && eq_token == parser.TreeToken("=")
        -> format_let_binding(children, ctx)
        _ -> format_inline(tree, ctx)
      }

    // Default: format inline
    _ -> format_inline(tree, ctx)
  }
}

fn format_lambda(children: List(parser.ParseTree), ctx: FormatContext) -> String {
  case children {
    [
      parser.TreeToken("\\"),
      parser.TreeToken(param),
      parser.TreeToken("."),
      body,
    ] -> "\\" <> param <> ". " <> format_node(body, ctx)
    _ -> format_inline(parser.TreeNode("Term", children), ctx)
  }
}

fn format_let_binding(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [
      parser.TreeToken("let"),
      parser.TreeToken(name),
      parser.TreeToken("="),
      expr,
    ] -> "let " <> name <> " = " <> format_node(expr, ctx)
    _ -> format_inline(parser.TreeNode("Start", children), ctx)
  }
}

// ============================================================================
// COMBINATORS
// ============================================================================

/// Sequence: format with f1 then f2
pub fn seq(f1: Formatter, f2: Formatter) -> Formatter {
  Formatter(fn(tree, ctx) {
    f1.format(tree, ctx) <> " " <> f2.format(tree, ctx)
  })
}

/// Choice: use first formatter
pub fn choice(f1: Formatter, _f2: Formatter) -> Formatter {
  f1
}

/// Optional: format or empty
pub fn opt(f: Formatter) -> Formatter {
  f
}

/// Repetition: format list with separator
pub fn rep(_separator: String) -> Formatter {
  Formatter(fn(tree, _ctx) {
    case tree {
      parser.TreeToken(value) -> value
      parser.TreeNode(_, children) ->
        children
        |> list.map(fn(c) { format_inline(c, FormatContext(0, " ")) })
        |> string.join(" ")
    }
  })
}
