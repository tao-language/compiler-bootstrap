// ============================================================================
// GRAMMAR TESTS
// ============================================================================

import gleeunit
import gleeunit/should
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
  True |> should.be_true
}

pub fn start_test() {
  let g = grammar.new("Test") |> grammar.start("Expr")

  g.start |> should.equal("Expr")
  True |> should.be_true
}

pub fn indent_sensitive_test() {
  let g = grammar.new("Test") |> grammar.indent_sensitive

  g.indent_sensitive |> should.be_true
  True |> should.be_true
}

pub fn with_token_test() {
  let g = grammar.new("Test") |> grammar.with_token("Ident")

  list.contains(g.tokens, "Ident") |> should.be_true
  True |> should.be_true
}

pub fn with_keyword_test() {
  let g = grammar.new("Test") |> grammar.with_keyword("let")

  list.contains(g.keywords, "let") |> should.be_true
  True |> should.be_true
}

pub fn rule_test() {
  let g = grammar.new("Test")
    |> grammar.rule("Expr", grammar.token("Ident"))

  list.contains(grammar.rule_names(g), "Expr") |> should.be_true
  True |> should.be_true
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

pub fn simple_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result = parse(tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn seq_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([grammar.token("Ident"), grammar.token("Operator")]))

  let parse = grammar.to_parser(g)
  let tokens = lexer.tokenize(lexer.default_config(), "test", "x +")
  let result = parse(tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

pub fn choice_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.choice([
      grammar.token("Ident"),
      grammar.token("Number"),
    ]))

  let parse = grammar.to_parser(g)

  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "hello")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "42")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])

  True |> should.be_true
}

pub fn opt_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.seq([
      grammar.token("Ident"),
      grammar.opt(grammar.token("Semicolon")),
    ]))

  let parse = grammar.to_parser(g)

  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "x")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "x ;")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])

  True |> should.be_true
}

pub fn many_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.many(grammar.token("Ident")))

  let parse = grammar.to_parser(g)

  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "a b c")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])

  True |> should.be_true
}

pub fn sep_by_grammar_parser_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.comma_sep(grammar.token("Ident")))

  let parse = grammar.to_parser(g)

  let tokens1 = lexer.tokenize(lexer.default_config(), "test", "a")
  let result1 = parse(tokens1)
  result1.errors |> should.equal([])

  let tokens2 = lexer.tokenize(lexer.default_config(), "test", "a , b , c")
  let result2 = parse(tokens2)
  result2.errors |> should.equal([])

  True |> should.be_true
}

pub fn expr_grammar_parser_test() {
  let g = grammar.new("Expr")
    |> grammar.start("Expr")
    |> grammar.rule("Expr", grammar.expr([
      parser.Atom("Number"),
      parser.InfixL("+", 10),
      parser.InfixL("*", 20),
    ]))

  let parse = grammar.to_parser(g)
  let config = lexer.default_config() |> lexer.with_keywords(["+", "*"])
  let tokens = lexer.tokenize(config, "test", "1 + 2 * 3")
  let result = parse(tokens)

  result.errors |> should.equal([])
  True |> should.be_true
}

// ============================================================================
// FORMATTER GENERATION TESTS
// ============================================================================

pub fn simple_grammar_formatter_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")
    |> grammar.rule("Start", grammar.token("Ident"))

  let format = grammar.to_formatter(g)
  let tree = parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0))

  let result = format(tree)
  string.contains(result, "hello") |> should.be_true
  True |> should.be_true
}

pub fn tree_formatter_test() {
  let g = grammar.new("Test")
    |> grammar.start("Start")

  let format = grammar.to_formatter(g)
  let tree = parser.Node("Seq", [
    parser.Leaf(parser.Token("Ident", "hello", fake_location(), 0)),
    parser.Leaf(parser.Token("Ident", "world", fake_location(), 0)),
  ])

  let result = format(tree)
  string.contains(result, "hello") |> should.be_true
  string.contains(result, "world") |> should.be_true
  True |> should.be_true
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
  True |> should.be_true
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn fake_location() -> parser.Location {
  parser.Location("unknown", parser.Position(1, 1, 0), parser.Position(1, 1, 0))
}
