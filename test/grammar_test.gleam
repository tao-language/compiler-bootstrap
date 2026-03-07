// ============================================================================
// GRAMMAR TESTS
// ============================================================================

import gleeunit
import gleeunit/should
import gleam/dict
import gleam/list
import gleam/string
import grammar
import lexer
import parser

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// GRAMMAR CONSTRUCTION TESTS
// ============================================================================

pub fn new_grammar_test() {
  let g = grammar.new("Test")

  g.name |> should.equal("Test")
  g.start |> should.equal("Start")
  dict.size(g.rules) |> should.equal(0)
}

pub fn start_test() {
  let g = grammar.new("Test") |> grammar.start("Expr")

  g.start |> should.equal("Expr")
}

pub fn indent_sensitive_test() {
  let g = grammar.new("Test") |> grammar.indent_sensitive

  g.indent_sensitive |> should.be_true
}

pub fn with_token_test() {
  let g = grammar.new("Test") |> grammar.with_token("Ident")

  list.contains(g.tokens, "Ident") |> should.be_true
}

pub fn with_keyword_test() {
  let g = grammar.new("Test") |> grammar.with_keyword("let")

  list.contains(g.keywords, "let") |> should.be_true
}

pub fn rule_test() {
  let g = grammar.new("Test")
    |> grammar.rule("Expr", grammar.token("Ident"))

  list.contains(grammar.rule_names(g), "Expr") |> should.be_true
}

// ============================================================================
// SYMBOL CONSTRUCTOR TESTS
// ============================================================================

pub fn token_symbol_test() {
  grammar.token("Ident") |> should.equal(grammar.Token("Ident"))
}

pub fn keyword_symbol_test() {
  grammar.keyword("let") |> should.equal(grammar.Keyword("let"))
}

pub fn ref_symbol_test() {
  grammar.ref("Expr") |> should.equal(grammar.Ref("Expr"))
}

pub fn seq_symbol_test() {
  grammar.seq([grammar.token("a"), grammar.token("b")])
    |> should.equal(grammar.Seq([grammar.Token("a"), grammar.Token("b")]))
}

pub fn choice_symbol_test() {
  grammar.choice([grammar.token("a"), grammar.token("b")])
    |> should.equal(grammar.Choice([grammar.Token("a"), grammar.Token("b")]))
}

pub fn opt_symbol_test() {
  grammar.opt(grammar.token("x")) |> should.equal(grammar.Opt(grammar.Token("x")))
}

pub fn many_symbol_test() {
  grammar.many(grammar.token("x")) |> should.equal(grammar.Many(grammar.Token("x")))
}

pub fn many1_symbol_test() {
  grammar.many1(grammar.token("x")) |> should.equal(grammar.Many1(grammar.Token("x")))
}

pub fn sep_symbol_test() {
  grammar.sep(grammar.token("item"), grammar.token(","))
    |> should.equal(grammar.Sep(grammar.Token("item"), grammar.Token(",")))
}

pub fn sep1_symbol_test() {
  grammar.sep1(grammar.token("item"), grammar.token(","))
    |> should.equal(grammar.Sep1(grammar.Token("item"), grammar.Token(",")))
}

pub fn comma_sep_symbol_test() {
  grammar.comma_sep(grammar.token("item"))
    |> should.equal(grammar.Sep1(grammar.Token("item"), grammar.Token("Comma")))
}

pub fn indent_block_symbol_test() {
  grammar.indent_block(grammar.token("stmt"))
    |> should.equal(grammar.IndentBlock(grammar.Token("stmt")))
}

pub fn label_symbol_test() {
  grammar.label("name", grammar.token("x"))
    |> should.equal(grammar.Label("name", grammar.Token("x")))
}

// ============================================================================
// EXPRESSION OPERATOR TESTS
// ============================================================================

pub fn atom_op_test() {
  parser.Atom("Number") |> should.equal(parser.Atom("Number"))
}

pub fn prefix_op_test() {
  parser.Prefix("-", 100) |> should.equal(parser.Prefix("-", 100))
}

pub fn postfix_op_test() {
  parser.Postfix("!", 90) |> should.equal(parser.Postfix("!", 90))
}

pub fn infix_l_op_test() {
  parser.InfixL("+", 50) |> should.equal(parser.InfixL("+", 50))
}

pub fn infix_r_op_test() {
  parser.InfixR("^", 60) |> should.equal(parser.InfixR("^", 60))
}

pub fn expr_symbol_test() {
  let ops = [parser.Atom("Number"), parser.InfixL("+", 50)]
  grammar.expr(ops) |> should.equal(grammar.Expr(ops))
}

// ============================================================================
// PARSER GENERATION TESTS
// ============================================================================

pub fn parse_ident_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parse(tokens)

  result.errors |> should.equal([])
  // Token rules produce just Leaf(token)
  case result.ast {
    parser.Leaf(token) -> token.value |> should.equal("hello")
    _ -> panic as "Expected Leaf token"
  }
}

pub fn parse_number_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "42")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(token) -> token.value |> should.equal("42")
    _ -> panic as "Expected Leaf token"
  }
}

pub fn parse_sequence_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.token("Operator"),
    ]))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x +")
  let result = parse(tokens)

  result.errors |> should.equal([])
  // Sequence creates Node("Seq", ...)
  case result.ast {
    parser.Node("Seq", children) -> list.length(children) |> should.equal(2)
    _ -> panic as "Expected Seq node with 2 children"
  }
}

pub fn parse_choice_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.choice([
      grammar.token("Ident"),
      grammar.token("Number"),
    ]))

  let parse = grammar.to_parser(g)

  // Test Ident branch
  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  // Test Number branch
  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "42")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])
}

pub fn parse_optional_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.opt(grammar.token("Semicolon")),
    ]))

  let parse = grammar.to_parser(g)

  // Without semicolon
  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "x")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  // With semicolon
  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "x ;")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])
}

pub fn parse_many_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let parse = grammar.to_parser(g)

  // Empty
  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  // Multiple
  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])
}

pub fn parse_sep_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let parse = grammar.to_parser(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let result = parse(tokens)
  result.errors |> should.equal([])
}

// ============================================================================
// FORMATTER GENERATION TESTS
// ============================================================================

pub fn format_ident_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let format = grammar.to_formatter(g)
  let tree = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0))
  ])

  let result = format(tree)
  result |> should.equal("hello")
}

pub fn format_number_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let format = grammar.to_formatter(g)
  let tree = parser.Node("Start", [
    parser.Leaf(parser.Token("Number", "42", fake_location(), 0))
  ])

  let result = format(tree)
  result |> should.equal("42")
}

pub fn format_sequence_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.token("Operator"),
    ]))

  let format = grammar.to_formatter(g)
  let tree = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "x", fake_location(), 0)),
    parser.Leaf(parser.Token("Operator", "+", fake_location(), 0)),
  ])

  let result = format(tree)
  result |> should.equal("x +")
}

pub fn format_choice_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.choice([
      grammar.token("Ident"),
      grammar.token("Number"),
    ]))

  let format = grammar.to_formatter(g)

  // Format Ident
  let tree1 = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0))
  ])
  format(tree1) |> should.equal("hello")

  // Format Number
  let tree2 = parser.Node("Start", [
    parser.Leaf(parser.Token("Number", "42", fake_location(), 0))
  ])
  format(tree2) |> should.equal("42")
}

pub fn format_optional_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.opt(grammar.token("Semicolon")),
    ]))

  let format = grammar.to_formatter(g)

  // Without semicolon
  let tree1 = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "x", fake_location(), 0)),
    parser.Empty,
  ])
  string.contains(format(tree1), "x") |> should.be_true

  // With semicolon
  let tree2 = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "x", fake_location(), 0)),
    parser.Leaf(parser.Token("Semicolon", ";", fake_location(), 0)),
  ])
  string.contains(format(tree2), "x") |> should.be_true
  string.contains(format(tree2), ";") |> should.be_true
}

pub fn format_many_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let format = grammar.to_formatter(g)

  // Multiple identifiers
  let tree = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "a", fake_location(), 0)),
    parser.Leaf(parser.Token("Ident", "b", fake_location(), 0)),
    parser.Leaf(parser.Token("Ident", "c", fake_location(), 0)),
  ])
  let result = format(tree)
  string.contains(result, "a") |> should.be_true
  string.contains(result, "b") |> should.be_true
  string.contains(result, "c") |> should.be_true
}

pub fn format_sep_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let format = grammar.to_formatter(g)

  let tree = parser.Node("Start", [
    parser.Leaf(parser.Token("Ident", "a", fake_location(), 0)),
    parser.Leaf(parser.Token("Ident", "b", fake_location(), 0)),
    parser.Leaf(parser.Token("Ident", "c", fake_location(), 0)),
  ])
  let result = format(tree)
  string.contains(result, "a") |> should.be_true
  string.contains(result, "b") |> should.be_true
  string.contains(result, "c") |> should.be_true
}

// ============================================================================
// PARSER-FORMATTER ROUND TRIP TESTS
// ============================================================================

pub fn round_trip_ident_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "hello"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)

  parse_result.errors |> should.equal([])

  let formatted = format(parse_result.ast)
  formatted |> should.equal("hello")
}

pub fn round_trip_number_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "42"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)

  parse_result.errors |> should.equal([])

  let formatted = format(parse_result.ast)
  formatted |> should.equal("42")
}

pub fn round_trip_sequence_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.token("Operator"),
    ]))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "x +"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)

  parse_result.errors |> should.equal([])

  let formatted = format(parse_result.ast)
  // Formatted output should contain both tokens
  string.contains(formatted, "x") |> should.be_true
  string.contains(formatted, "+") |> should.be_true
}

pub fn round_trip_choice_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.choice([
      grammar.token("Ident"),
      grammar.token("Number"),
    ]))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  // Test Ident branch
  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])
  format(result1.ast) |> should.equal("hello")

  // Test Number branch
  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "42")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])
  format(result2.ast) |> should.equal("42")
}

pub fn round_trip_optional_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.opt(grammar.token("Semicolon")),
    ]))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  // Without semicolon
  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "x")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])
  string.contains(format(result1.ast), "x") |> should.be_true

  // With semicolon
  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "x ;")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])
  string.contains(format(result2.ast), "x") |> should.be_true
  string.contains(format(result2.ast), ";") |> should.be_true
}

pub fn round_trip_many_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  // Multiple identifiers
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result = parse(tokens)
  result.errors |> should.equal([])

  let formatted = format(result.ast)
  string.contains(formatted, "a") |> should.be_true
  string.contains(formatted, "b") |> should.be_true
  string.contains(formatted, "c") |> should.be_true
}

pub fn round_trip_sep_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let result = parse(tokens)
  result.errors |> should.equal([])

  let formatted = format(result.ast)
  string.contains(formatted, "a") |> should.be_true
  string.contains(formatted, "b") |> should.be_true
  string.contains(formatted, "c") |> should.be_true
}

// ============================================================================
// VALIDATION TESTS
// ============================================================================

pub fn validate_valid_grammar_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.ref("Expr"))
    |> grammar.rule("Expr", grammar.token("Ident"))

  grammar.validate(g) |> should.be_ok
}

pub fn validate_invalid_grammar_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.ref("Missing"))

  grammar.validate(g) |> should.be_error
}

// ============================================================================
// UTILITY TESTS
// ============================================================================

pub fn rule_names_test() {
  let g = grammar.new("Test")
    |> grammar.rule("A", grammar.token("x"))
    |> grammar.rule("B", grammar.token("y"))

  let names = grammar.rule_names(g)
  list.contains(names, "A") |> should.be_true
  list.contains(names, "B") |> should.be_true
  list.length(names) |> should.equal(2)
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn fake_location() -> parser.Location {
  parser.Location("unknown", parser.Position(1, 1, 0), parser.Position(1, 1, 0))
}
