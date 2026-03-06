// ============================================================================
// FORMATTER TESTS
// ============================================================================

import formatter
import gleeunit
import gleeunit/should
import parser

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// BASIC FORMATTER TESTS
// ============================================================================

pub fn format_token_test() {
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "hello",
      parser.Position(1, 1, 0),
    ))
  formatter.format_token(tree, formatter.new_context()) |> should.equal("hello")
}

pub fn format_inline_test() {
  let tree =
    parser.TreeNode("Seq", [
      parser.TreeToken(parser.Token(
        parser.TokenIdent,
        "a",
        parser.Position(1, 1, 0),
      )),
      parser.TreeToken(parser.Token(
        parser.TokenIdent,
        "b",
        parser.Position(1, 3, 2),
      )),
    ])
  formatter.format_inline(tree, formatter.new_context()) |> should.equal("a b")
}

pub fn format_block_test() {
  let tree =
    parser.TreeNode("Seq", [
      parser.TreeToken(parser.Token(
        parser.TokenIdent,
        "a",
        parser.Position(1, 1, 0),
      )),
      parser.TreeToken(parser.Token(
        parser.TokenIdent,
        "b",
        parser.Position(2, 1, 0),
      )),
    ])
  formatter.format_block(tree, formatter.new_context())
  |> should.equal("  a\n  b")
}

pub fn format_identity_test() {
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "test",
      parser.Position(1, 1, 0),
    ))
  formatter.format(tree) |> should.equal("test")
}

// ============================================================================
// FORMATTER COMBINATOR TESTS
// ============================================================================

pub fn seq_formatter_test() {
  let f1 = formatter.Formatter(formatter.format_inline)
  let f2 = formatter.Formatter(formatter.format_inline)
  let f = formatter.seq(f1, f2)
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "test",
      parser.Position(1, 1, 0),
    ))
  let result = f.format(tree, formatter.new_context())
  result |> should.equal("test test")
}

pub fn choice_formatter_test() {
  let f1 = formatter.Formatter(formatter.format_inline)
  let f2 = formatter.Formatter(formatter.format_block)
  let f = formatter.choice(f1, f2)
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "test",
      parser.Position(1, 1, 0),
    ))
  f.format(tree, formatter.new_context()) |> should.equal("test")
}

pub fn opt_formatter_test() {
  let f = formatter.opt(formatter.Formatter(formatter.format_inline))
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "opt",
      parser.Position(1, 1, 0),
    ))
  f.format(tree, formatter.new_context()) |> should.equal("opt")
}

pub fn rep_formatter_test() {
  let f = formatter.rep(", ")
  let tree =
    parser.TreeToken(parser.Token(
      parser.TokenIdent,
      "test",
      parser.Position(1, 1, 0),
    ))
  f.format(tree, formatter.new_context()) |> should.equal("test")
}
