// ============================================================================
// TAO LEXER
// ============================================================================
/// Tao language lexer.
///
/// The lexer is language-agnostic and lives in src/syntax/lexer.gleam.
/// This module provides Tao-specific keyword handling.
///
/// For detailed documentation see:
/// - [Syntax Library](../../docs/syntax-library.md)
/// - [Tao Overloading](../../docs/plans/tao/10-overloading-design.md)
import syntax/lexer.{type Token, tokenize as lexer_tokenize}
import gleam/list

// ============================================================================
// PUBLIC API
// ============================================================================

/// Tokenize Tao source code.
///
/// The syntax library lexer handles all basic tokenization.
/// Keywords are identified during parsing, not lexing.
pub fn tokenize(source: String) -> List(Token) {
  lexer_tokenize(source)
}

// ============================================================================
// TAO KEYWORDS
// ============================================================================

/// List of Tao keywords.
///
/// These are reserved and cannot be used as identifiers.
pub const keywords = [
  "fn",
  "let",
  "mut",
  "match",
  "if",
  "else",
  "type",
  "import",
  "export",
  "as",
  "comptime",
  "true",
  "false",
]

/// Check if a string is a Tao keyword.
pub fn is_keyword(name: String) -> Bool {
  list.contains(keywords, name)
}

// ============================================================================
// TAO OPERATORS
// ============================================================================

/// List of Tao operators.
///
/// Used by the grammar for operator precedence parsing.
pub const operators = [
  // Arithmetic
  "+", "-", "*", "/", "%",
  // Comparison
  "==", "!=", "<", ">", "<=", ">=",
  // Logical
  "&&", "||", "!",
  // Assignment
  "=", "+=", "-=", "*=", "/=",
  // Other
  "->", "=>", ".", ",", ":", ";",
  // Delimiters
  "(", ")", "{", "}", "[", "]",
  // Pattern matching
  "|", "@", "..",
  // Type system
  "<", ">",
  // Null coalescing
  "??",
  // Optional chaining
  "?.",
  // Import path separator
  "/",
  // Wildcard
  "*",
]
