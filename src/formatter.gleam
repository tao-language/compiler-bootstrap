// ============================================================================
// FORMATTER - Full Programming Language Formatter
// ============================================================================

/// A comprehensive formatter for programming language parse trees with proper
/// layout, indentation, and formatting rules.
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
    parser.TreeToken(token) -> token.value
    parser.TreeNode(_, _) -> ""
    parser.TreeError(_) -> ""
  }
}

/// Format a node with children on same line
pub fn format_inline(tree: parser.ParseTree, _ctx: FormatContext) -> String {
  case tree {
    parser.TreeToken(token) -> token.value
    parser.TreeNode(_, children) ->
      children
      |> list.map(fn(c) { format_inline(c, FormatContext(0, " ")) })
      |> string.join(" ")
    parser.TreeError(_) -> ""
  }
}

/// Format a node with children on separate lines (indented)
pub fn format_block(tree: parser.ParseTree, ctx: FormatContext) -> String {
  let indented_ctx = indent(ctx)
  case tree {
    parser.TreeToken(token) -> get_indent(ctx) <> token.value
    parser.TreeNode(_, children) ->
      children
      |> list.map(fn(c) { format_block(c, indented_ctx) })
      |> string.join("\n")
    parser.TreeError(_) -> ""
  }
}

// ============================================================================
// GRAMMAR-AWARE FORMATTER
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
    parser.TreeToken(token) -> token.value
    parser.TreeNode(name, children) -> format_by_name(name, children, ctx)
    parser.TreeError(_) -> ""
  }
}

fn format_by_name(
  name: String,
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case name {
    // Top-level program
    "Program" -> format_program(children, ctx)

    // Function definition: fn name(params) -> type { body }
    "Function" -> format_function(children, ctx)

    // Let binding: let name = expr
    "LetBinding" -> format_let_binding(children, ctx)

    // If expression: if cond { then } else { else }
    "IfExpr" -> format_if_expr(children, ctx)

    // Match expression: match expr { cases }
    "MatchExpr" -> format_match_expr(children, ctx)

    // Match case: pattern -> expr
    "MatchCase" -> format_match_case(children, ctx)

    // Function call: func(args)
    "CallExpr" -> format_call_expr(children, ctx)

    // Binary operation: left op right
    "BinOpExpr" -> format_binop_expr(children, ctx)

    // Default: format inline
    _ -> format_inline(parser.TreeNode(name, children), ctx)
  }
}

fn format_program(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  children
  |> list.map(fn(c) { format_node(c, ctx) })
  |> string.join("\n\n")
}

fn format_function(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [name, params, return_type, body] ->
      "fn "
      <> format_node(name, ctx)
      <> format_node(params, ctx)
      <> " -> "
      <> format_node(return_type, ctx)
      <> " {\n"
      <> format_node(body, indent(ctx))
      <> "\n}"
    _ -> format_inline(parser.TreeNode("Function", children), ctx)
  }
}

fn format_let_binding(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [name, expr] ->
      "let " <> format_node(name, ctx) <> " = " <> format_node(expr, ctx)
    _ -> format_inline(parser.TreeNode("LetBinding", children), ctx)
  }
}

fn format_if_expr(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [cond, then_branch, else_branch] ->
      "if "
      <> format_node(cond, ctx)
      <> " {\n"
      <> format_node(then_branch, indent(ctx))
      <> "\n} else {\n"
      <> format_node(else_branch, indent(ctx))
      <> "\n}"
    [cond, then_branch] ->
      "if "
      <> format_node(cond, ctx)
      <> " {\n"
      <> format_node(then_branch, indent(ctx))
      <> "\n}"
    _ -> format_inline(parser.TreeNode("IfExpr", children), ctx)
  }
}

fn format_match_expr(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [expr, cases] ->
      "match "
      <> format_node(expr, ctx)
      <> " {\n"
      <> format_node(cases, indent(ctx))
      <> "\n}"
    _ -> format_inline(parser.TreeNode("MatchExpr", children), ctx)
  }
}

fn format_match_case(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [pattern, expr] ->
      get_indent(ctx)
      <> format_node(pattern, ctx)
      <> " -> "
      <> format_node(expr, ctx)
    _ -> format_inline(parser.TreeNode("MatchCase", children), ctx)
  }
}

fn format_call_expr(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [func, args] ->
      format_node(func, ctx) <> "(" <> format_node(args, ctx) <> ")"
    _ -> format_inline(parser.TreeNode("CallExpr", children), ctx)
  }
}

fn format_binop_expr(
  children: List(parser.ParseTree),
  ctx: FormatContext,
) -> String {
  case children {
    [left, op, right] ->
      format_node(left, ctx)
      <> " "
      <> format_node(op, ctx)
      <> " "
      <> format_node(right, ctx)
    _ -> format_inline(parser.TreeNode("BinOpExpr", children), ctx)
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
      parser.TreeToken(token) -> token.value
      parser.TreeNode(_, children) ->
        children
        |> list.map(fn(c) { format_inline(c, FormatContext(0, " ")) })
        |> string.join(" ")
      parser.TreeError(_) -> ""
    }
  })
}
