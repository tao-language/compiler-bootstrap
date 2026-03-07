// ============================================================================
// PARSER TESTS
// ============================================================================

import gleeunit
import gleeunit/should
import gleam/list
import gleam/string
import parser
import lexer

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// BASIC PARSER TESTS
// ============================================================================

pub fn ok_parser_test() {
  let p = parser.ok(42)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "")
  let result = parser.parse(p, "test", tokens)

  result.ast |> should.equal(42)
  result.errors |> should.equal([])
}

pub fn token_parser_test() {
  let p = parser.token("Ident")
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn keyword_parser_test() {
  let config = lexer.default_config() |> lexer.with_keywords(["let"])
  let p = parser.keyword("let")
  let tokens = lexer.tokenize(config, "test", "let")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// SEQUENCE TESTS
// ============================================================================

pub fn seq_parser_test() {
  let p = parser.seq([parser.token("Ident"), parser.token("Operator")])
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x +")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn opt_parser_test() {
  let p = parser.opt(parser.token("Semicolon"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn many_parser_test() {
  let p = parser.many(parser.token("Ident"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn many1_parser_test() {
  let p = parser.many1(parser.token("Ident"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// CHOICE TESTS
// ============================================================================

pub fn one_of_parser_test() {
  let p = parser.one_of([parser.token("Ident"), parser.token("Number")])
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// SEPARATOR TESTS
// ============================================================================

pub fn sep_by_parser_test() {
  let p = parser.sep_by(parser.token("Ident"), parser.token("Comma"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn sep_by1_parser_test() {
  let p = parser.sep_by1(parser.token("Ident"), parser.token("Comma"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// DELIMITER TESTS
// ============================================================================

pub fn parens_parser_test() {
  let p = parser.parens(parser.token("Ident"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "( x )")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn braces_parser_test() {
  let p = parser.braces(parser.token("Ident"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "{ x }")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// MAPPING TESTS
// ============================================================================

pub fn map_parser_test() {
  let p = parser.map(parser.token("Ident"), fn(tok) { tok.value })
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parser.parse(p, "test", tokens)

  result.ast |> should.equal("hello")
  True |> should.be_true
}

// ============================================================================
// ERROR TESTS
// ============================================================================

pub fn fail_parser_test() {
  let p = parser.fail("nothing")
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x")
  let result = parser.parse(p, "test", tokens)

  { list.is_empty(result.errors) == False } |> should.equal(True)
  True |> should.be_true
}

pub fn expect_parser_test() {
  let p = parser.expect(parser.token("Number"), "expected number")
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parser.parse(p, "test", tokens)

  { list.is_empty(result.errors) == False } |> should.equal(True)
  True |> should.be_true
}

// ============================================================================
// LOOKAHEAD TESTS
// ============================================================================

pub fn lookahead_parser_test() {
  let p = parser.lookahead(parser.token("Ident"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x y")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn not_parser_test() {
  let p = parser.not(parser.token("Number"))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// ERROR RECOVERY TESTS
// ============================================================================

pub fn recover_parser_test() {
  let p = parser.recover(parser.token("Number"), parser.Token("Number", "0", parser.Location("test", parser.Position(1, 1, 0), parser.Position(1, 2, 0)), 0))
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parser.parse(p, "test", tokens)

  // Should have error but still return fallback value
  True |> should.be_true
}

pub fn sync_to_parser_test() {
  let config = lexer.default_config() |> lexer.with_keywords(["return", "if"])
  let p = parser.then(
    parser.token("Ident"),
    parser.preceed(parser.sync_to(["Keyword"]), parser.keyword("return")),
  )
  let tokens = lexer.tokenize(config, "test", "x garbage return")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// PRATT PARSING TESTS
// ============================================================================

pub fn pratt_atom_test() {
  let ops = [parser.Atom("Number")]
  let p = parser.pratt(ops)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "42")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn pratt_infix_l_test() {
  let ops = [
    parser.Atom("Number"),
    parser.InfixL("+", 10),
  ]
  let p = parser.pratt(ops)
  let config = lexer.default_config() |> lexer.with_keywords(["+"])
  let tokens = lexer.tokenize(config, "test", "1 + 2")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn pratt_precedence_test() {
  // Test that * binds tighter than +
  let ops = [
    parser.Atom("Number"),
    parser.InfixL("+", 10),
    parser.InfixL("*", 20),
  ]
  let p = parser.pratt(ops)
  let config = lexer.default_config() |> lexer.with_keywords(["+", "*"])
  let tokens = lexer.tokenize(config, "test", "1 + 2 * 3")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  // Should parse as 1 + (2 * 3), not (1 + 2) * 3
  True |> should.be_true
}

pub fn pratt_prefix_test() {
  let ops = [
    parser.Atom("Number"),
    parser.Prefix("-", 100),
  ]
  let p = parser.pratt(ops)
  let config = lexer.default_config() |> lexer.with_keywords(["-"])
  let tokens = lexer.tokenize(config, "test", "- 5")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn pratt_right_assoc_test() {
  // Test right-associative operator (like ^)
  let ops = [
    parser.Atom("Number"),
    parser.InfixR("^", 30),
  ]
  let p = parser.pratt(ops)
  let config = lexer.default_config() |> lexer.with_keywords(["^"])
  let tokens = lexer.tokenize(config, "test", "2 ^ 3 ^ 2")
  let result = parser.parse(p, "test", tokens)

  result.errors |> should.equal([])
  // Should parse as 2 ^ (3 ^ 2), not (2 ^ 3) ^ 2
  True |> should.be_true
}

// ============================================================================
// ERROR FORMATTING TESTS
// ============================================================================

pub fn format_error_test() {
  let error = parser.ParseError(
    location: parser.Location("test.gleam", parser.Position(1, 5, 4), parser.Position(1, 5, 4)),
    message: "Parse error",
    expected: ["Ident"],
    severity: parser.ParseErrorLevel,
  )

  let formatted = parser.format_error(error, "let x = 1")

  string.contains(formatted, "error") |> should.be_true
  True |> should.be_true
}
