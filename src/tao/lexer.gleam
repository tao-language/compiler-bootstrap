// Tao Lexer - Tokenizer for the Tao language
// Uses the syntax/lexer module as a foundation

import syntax/lexer.{tokenize, type Token as SyntaxToken}
import syntax/span.{type Span, dummy}
import gleam/list

// ============================================================================
// TAo TOKENS
// ============================================================================

/// Tao-specific token kinds
pub type TaoKind {
  Keyword
  Identifier
  Number
  String
  Operator
  Punctuation
  Literal
  Comment
  Unknown
}

/// Tao token
pub type Token {
  Token(kind: TaoKind, value: String, span: Span)
}

// ============================================================================
// TAo LEXER
// ============================================================================

/// Tokenize Tao source
pub fn tao_tokenize(source: String, file: String) -> List(Token) {
  let tokens = tokenize(source, file)
  list.map(tokens, fn(t: SyntaxToken) {
    let kind = to_tao_kind(t.kind, t.value)
    let span = dummy()
    Token(kind: kind, value: t.value, span: span)
  })
}

/// Convert a syntax token kind to a Tao token kind
fn to_tao_kind(kind: String, value: String) -> TaoKind {
  case kind, value {
    "Keyword", _ -> Keyword
    "Ident", _ -> Identifier
    "Number", _ -> Number
    "String", _ -> String
    "Operator", _ -> Operator
    "Punctuation", _ -> Punctuation
    "Literal", _ -> Literal
    "Comment", _ -> Comment
    _kind, _value -> Unknown
  }
}
