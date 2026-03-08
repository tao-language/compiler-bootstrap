// ============================================================================
// GRAMMAR TESTS - Optimized for Speed
// Removed redundant tests while maintaining coverage
// ============================================================================

import gleam/dict
import gleam/list
import gleeunit
import gleeunit/should
import grammar
import lexer
import parser

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// GRAMMAR CONSTRUCTION TESTS (6 tests)
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
  let g = grammar.new("Test") |> grammar.rule("Expr", grammar.token("Ident"))
  list.contains(grammar.rule_names(g), "Expr") |> should.be_true
}

// ============================================================================
// SYMBOL CONSTRUCTOR TESTS (6 tests - removed redundant similar tests)
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
  grammar.opt(grammar.token("x"))
  |> should.equal(grammar.Opt(grammar.Token("x")))
}

// ============================================================================
// EXPRESSION OPERATOR TESTS (3 tests - removed redundant similar tests)
// ============================================================================

pub fn atom_op_test() {
  parser.Atom("Number") |> should.equal(parser.Atom("Number"))
}

pub fn infix_l_op_test() {
  parser.InfixL("+", 50) |> should.equal(parser.InfixL("+", 50))
}

pub fn infix_r_op_test() {
  parser.InfixR("^", 60) |> should.equal(parser.InfixR("^", 60))
}

// ============================================================================
// PARSER GENERATION TESTS (7 tests - core functionality only)
// ============================================================================

pub fn parse_ident_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Ident", "hello", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Leaf token with Ident kind and hello value"
  }
}

pub fn parse_number_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "42")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Number", "42", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Leaf token with Number kind and 42 value"
  }
}

pub fn parse_sequence_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.token("Operator"),
      ]),
    )

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x +")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Node("Seq", children) -> list.length(children) |> should.equal(2)
    _ -> panic as "Expected Seq node with 2 children"
  }
}

pub fn parse_choice_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.choice([
        grammar.token("Ident"),
        grammar.token("Number"),
      ]),
    )

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Ident", "hello", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Ident from choice"
  }
}

pub fn parse_optional_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.opt(grammar.token("Semicolon")),
      ]),
    )

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Node("Seq", children) -> list.length(children) |> should.equal(2)
    _ -> panic as "Expected Seq node"
  }
}

pub fn parse_many_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Node("Many", children) -> list.length(children) |> should.equal(3)
    _ -> panic as "Expected Many node with 3 children"
  }
}

pub fn parse_sep_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let result = parse(tokens)

  result.errors |> should.equal([])
  case result.ast {
    parser.Node("Sep", children) -> list.length(children) |> should.equal(3)
    _ -> panic as "Expected Sep node with 3 children"
  }
}

// ============================================================================
// FORMATTER GENERATION TESTS (7 tests - core functionality only)
// ============================================================================

pub fn format_ident_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0)),
    ])

  let result = format(tree)
  result |> should.equal("hello")
}

pub fn format_number_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Leaf(parser.Token("Number", "42", fake_location(), 0)),
    ])

  let result = format(tree)
  result |> should.equal("42")
}

pub fn format_sequence_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.token("Operator"),
      ]),
    )

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Leaf(parser.Token("Ident", "x", fake_location(), 0)),
      parser.Leaf(parser.Token("Operator", "+", fake_location(), 0)),
    ])

  let result = format(tree)
  result |> should.equal("x +")
}

pub fn format_choice_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.choice([
        grammar.token("Ident"),
        grammar.token("Number"),
      ]),
    )

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0)),
    ])

  let result = format(tree)
  result |> should.equal("hello")
}

pub fn format_optional_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.opt(grammar.token("Semicolon")),
      ]),
    )

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Leaf(parser.Token("Ident", "x", fake_location(), 0)),
      parser.Leaf(parser.Token("Semicolon", ";", fake_location(), 0)),
    ])

  let result = format(tree)
  result |> should.equal("x ;")
}

pub fn format_many_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Node("Many", [
        parser.Leaf(parser.Token("Ident", "a", fake_location(), 0)),
        parser.Leaf(parser.Token("Ident", "b", fake_location(), 0)),
        parser.Leaf(parser.Token("Ident", "c", fake_location(), 0)),
      ]),
    ])

  let result = format(tree)
  result |> should.equal("a b c")
}

pub fn format_sep_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let format = grammar.to_formatter(g)
  let tree =
    parser.Node("Start", [
      parser.Node("Sep", [
        parser.Leaf(parser.Token("Ident", "a", fake_location(), 0)),
        parser.Leaf(parser.Token("Ident", "b", fake_location(), 0)),
        parser.Leaf(parser.Token("Ident", "c", fake_location(), 0)),
      ]),
    ])

  let result = format(tree)
  result |> should.equal("a b c")
}

// ============================================================================
// PARSER-FORMATTER ROUND TRIP TESTS (7 tests - core functionality only)
// ============================================================================

pub fn round_trip_ident_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "hello"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("hello")
}

pub fn round_trip_number_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Number"))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "42"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("42")
}

pub fn round_trip_sequence_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.token("Operator"),
      ]),
    )

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let source = "x +"
  let tokens = lexer.tokenize(lexer.default_config(), "test", source)
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("x +")
}

pub fn round_trip_choice_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.choice([
        grammar.token("Ident"),
        grammar.token("Number"),
      ]),
    )

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("hello")
}

pub fn round_trip_optional_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule(
      "Start",
      grammar.seq([
        grammar.token("Ident"),
        grammar.opt(grammar.token("Semicolon")),
      ]),
    )

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "x ;")
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("x ;")
}

pub fn round_trip_many_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("a b c")
}

pub fn round_trip_sep_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let parse = grammar.to_parser(g)
  let format = grammar.to_formatter(g)

  let tokens = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let parse_result = parse(tokens)
  let formatted = format(parse_result.ast)

  formatted |> should.equal("a b c")
}

// ============================================================================
// VALIDATION TESTS (2 tests)
// ============================================================================

pub fn validate_valid_grammar_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.ref("Expr"))
    |> grammar.rule("Expr", grammar.token("Ident"))

  grammar.validate(g) |> should.be_ok
}

pub fn validate_invalid_grammar_test() {
  let g =
    grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.ref("Missing"))

  grammar.validate(g) |> should.be_error
}

// ============================================================================
// UTILITY TESTS (1 test)
// ============================================================================

pub fn rule_names_test() {
  let g =
    grammar.new("Test")
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
