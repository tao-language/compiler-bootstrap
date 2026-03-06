// ============================================================================
// CORE LANGUAGE GRAMMAR
// ============================================================================

/// Defines the grammar for the core dependently typed language.
/// Uses the generic parser and formatter libraries.
import formatter
import parser

// ============================================================================
// GRAMMAR DEFINITION
// ============================================================================

/// Build the core language parser
pub fn parser() -> parser.Parser {
  program()
}

/// Program: list of declarations
fn program() -> parser.Parser {
  parser.rep(declaration())
}

/// Declaration: function or type definition
fn declaration() -> parser.Parser {
  parser.choice(function_def(), type_def())
}

/// Function definition: fn name(params) -> type { body }
fn function_def() -> parser.Parser {
  parser.seq4(
    parser.keyword("fn"),
    parser.label(parser.ident(), "name"),
    params(),
    parser.seq2(parser.token(parser.TokenArrow), simple_type()),
  )
  |> parser.map(fn(result) { parser.TreeNode("Function", [result]) })
}

/// Type definition: type Name = Type
fn type_def() -> parser.Parser {
  parser.seq4(
    parser.keyword("type"),
    parser.label(parser.ident(), "name"),
    parser.token(parser.TokenOperator("=")),
    simple_type(),
  )
  |> parser.map(fn(result) { parser.TreeNode("TypeDecl", [result]) })
}

/// Parameters: (x: Type, y: Type)
fn params() -> parser.Parser {
  parser.seq3(
    parser.token(parser.TokenLParen),
    parser.rep1(param()),
    parser.token(parser.TokenRParen),
  )
}

/// Parameter: x: Type
fn param() -> parser.Parser {
  parser.seq3(
    parser.label(parser.ident(), "name"),
    parser.token(parser.TokenColon),
    simple_type(),
  )
  |> parser.map(fn(result) { parser.TreeNode("Param", [result]) })
}

/// Simple type: identifier
fn simple_type() -> parser.Parser {
  parser.ident()
}

// ============================================================================
// FORMATTER
// ============================================================================

/// Format a core language parse tree
pub fn format(tree: parser.ParseTree) -> String {
  formatter.format(tree)
}

/// Format with custom context
pub fn format_with_context(
  tree: parser.ParseTree,
  ctx: formatter.FormatContext,
) -> String {
  formatter.format_with_context(tree, ctx)
}
