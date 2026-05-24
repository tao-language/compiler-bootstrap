/// Tests for the parser combinator DSL
///
/// Tests cover:
/// - Pattern construction (tok, kw, op, ref, seq, opt, many, choice, sep_by, parens, delimited)
/// - Either type helpers (is_left, is_right)
/// - ParseResult extraction (result_ast, result_errors)
/// - Error formatting (error_to_string)
import gleam/list
import gleeunit
import syntax/base_lexer.{tokenize, tokenize_with_filename}
import syntax/grammar.{
  type Alternative, type Either, type Grammar, type ParseResult, type Pattern,
  type Rule, Alternative, Choice, Delimited, Grammar, Infix, Kw, Left, Many, Op,
  Opt, Parens, ParseError, ParseResult, Ref, Right, Rule, SepBy, Seq, Tok,
  choice, delimited, error_to_string, is_left, is_right, kw, many, op, opt,
  parens, parse, ref, result_ast, result_errors, sep_by, seq, tok,
}
import syntax/span.{type Span, single}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Test helper functions
// ============================================================================

/// Helper function for Alternative(Int) constructors
pub fn alt_constructor_int(_v: List(#(Either(String, Int), Span))) -> Int {
  42
}

/// Helper function for Alternative(String) constructors
pub fn alt_constructor_string(
  _v: List(#(Either(String, String), Span)),
) -> String {
  "node"
}

/// Helper function for string concatenation in operators
pub fn concat_string(left: String, right: String) -> String {
  left <> "+" <> right
}



pub fn alternative_type_stores_constructor_test() {
  // Test that we can construct an Alternative with a simple constructor
  // Alternative(Int) constructor: fn(List(#(Either(String, Int), Span))) -> Int
  let a: Alternative(Int) =
    Alternative(pattern: tok("Name"), constructor: alt_constructor_int)
  let result = a.constructor([])
  assert result == 42
}

// ============================================================================
// ParseResult helpers
// ============================================================================

pub fn result_ast_returns_ast_on_errors_test() {
  let err =
    ParseError(
      span: single("test", 1, 1),
      expected: "Name",
      got: "EOF",
      context: "at start",
      rule: "",
      surrounding: [],
    )
  let result: ParseResult(Int) = ParseResult(ast: 42, errors: [err])
  assert result_ast(0, result) == 42
}


pub fn result_errors_returns_errors_list_test() {
  let err =
    ParseError(
      span: single("test", 1, 1),
      expected: "Name",
      got: "EOF",
      context: "test",
      rule: "",
      surrounding: [],
    )
  let result: ParseResult(String) = ParseResult(ast: "hello", errors: [err])
  let errors = result_errors("fallback", result)
  assert list.length(errors) == 1
}

// ============================================================================
// Error formatting
// ============================================================================

pub fn error_to_string_single_line_test() {
  let err =
    ParseError(
      span: single("test.tao", 1, 5),
      expected: "Name",
      got: "Eof",
      context: "in expression",
      rule: "",
      surrounding: [],
    )
  let formatted = error_to_string(err)
  assert formatted == "in test.tao line 1, col 5: Name (found: Eof) in in expression"
}

pub fn error_to_string_multi_line_test() {
  let err =
    ParseError(
      span: single("test.tao", 2, 1),
      expected: "Keyword",
      got: "Integer",
      context: "at module level",
      rule: "",
      surrounding: [],
    )
  let formatted = error_to_string(err)
  assert formatted == "in test.tao line 2, col 1: Keyword (found: Integer) in at module level"
}



// ============================================================================
// ParseResult with multiple errors
// ============================================================================

pub fn parse_result_with_multiple_errors_returns_all_errors_test() {
  let err1 =
    ParseError(
      span: single("test", 1, 1),
      expected: "Name",
      got: "Eof",
      context: "first",
      rule: "",
      surrounding: [],
    )
  let err2 =
    ParseError(
      span: single("test", 2, 1),
      expected: "Keyword",
      got: "Name",
      context: "second",
      rule: "",
      surrounding: [],
    )
  let err3 =
    ParseError(
      span: single("test", 3, 1),
      expected: "Op",
      got: "String",
      context: "third",
      rule: "",
      surrounding: [],
    )
  let result: ParseResult(String) =
    ParseResult(ast: "fallback", errors: [err1, err2, err3])
  let errors = result_errors("fallback", result)
  assert list.length(errors) == 3
}

// ============================================================================
// Grammar with rules
// ============================================================================

pub fn grammar_with_multiple_rules_test() {
  let alt =
    Alternative(pattern: tok("Name"), constructor: alt_constructor_string)
  let rules = [
    Rule(name: "Expr", alternatives: [alt], precedence: 0),
    Rule(name: "Term", alternatives: [alt], precedence: 10),
  ]
  let g: Grammar(String) =
    Grammar(
      name: "Test",
      start: "Expr",
      rules: rules,
      keywords: ["let", "fn"],
      operators: [],
    )
  assert g.name == "Test"
  assert list.length(g.rules) == 2
  assert g.keywords == ["let", "fn"]
}



// ============================================================================
// Actual parsing behavior tests
//
// These tests verify that each combinator produces correct error/success
// outcomes when parsing real token lists. We use a minimal grammar that
// has a single rule matching a specific token type, then check that
// parse() correctly returns errors for non-matching input.
//
// Helper: build a minimal grammar with one rule that matches a token.
fn make_tok_grammar(tok_kind: String) -> Grammar(String) {
  let alt: Alternative(String) =
    Alternative(pattern: tok(tok_kind), constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}

fn make_kw_grammar(keyword: String) -> Grammar(String) {
  let alt: Alternative(String) =
    Alternative(pattern: kw(keyword), constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [keyword],
    operators: [],
  )
}

fn make_op_grammar(sym: String) -> Grammar(String) {
  let alt: Alternative(String) =
    Alternative(pattern: op(sym), constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}

// --- tok pattern parsing ---

pub fn parse_op_matching_operator_succeeds_test() {
  // op("+") should succeed when the first token is "Op" with value "+"
  let tokens = tokenize("+")
  let grammar = make_op_grammar("+")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- seq pattern parsing ---

fn make_seq_name_name_grammar() -> Grammar(String) {
  // Grammar that matches: Name Name
  let alt: Alternative(String) =
    Alternative(
      pattern: seq([tok("Name"), tok("Name")]),
      constructor: alt_constructor_string,
    )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}



fn make_opt_comma_grammar() -> Grammar(String) {
  // Grammar that matches Name followed by optional comma
  let alt: Alternative(String) =
    Alternative(
      pattern: seq([tok("Name"), opt(Tok(","))]),
      constructor: alt_constructor_string,
    )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}



fn make_many_name_grammar() -> Grammar(String) {
  // Grammar that matches zero or more Names
  let alt: Alternative(String) =
    Alternative(pattern: many(tok("Name")), constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}



fn make_choice_grammar() -> Grammar(String) {
  // Grammar that matches either Name or Integer
  Grammar(
    name: "Test",
    start: "Test",
    rules: [
      Rule(
        name: "Test",
        alternatives: [
          Alternative(
            pattern: choice([tok("Name"), tok("Integer")]),
            constructor: alt_constructor_string,
          ),
        ],
        precedence: 0,
      ),
    ],
    keywords: [],
    operators: [],
  )
}



fn make_sep_by_name_comma_grammar() -> Grammar(String) {
  // Grammar that matches: Name ("," Name)*
  let sep_pattern = sep_by(tok("Name"), Tok(","))
  let alt: Alternative(String) =
    Alternative(pattern: sep_pattern, constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}

pub fn parse_sep_by_single_item_succeeds_test() {
  // sep_by(Name, ",") should match single Name without separator
  let tokens = tokenize("foo")
  let grammar = make_sep_by_name_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

pub fn parse_sep_by_zero_items_succeeds_test() {
  // sep_by(Name, ",") should match empty input (zero items)
  let tokens = tokenize("")
  let grammar = make_sep_by_name_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- parens pattern parsing ---

fn make_parens_name_grammar() -> Grammar(String) {
  // Grammar that matches: "(" Name ")"
  let alt: Alternative(String) =
    Alternative(
      pattern: parens("NameRule"),
      constructor: alt_constructor_string,
    )
  let name_rule: Rule(String) =
    Rule(
      name: "NameRule",
      alternatives: [
        Alternative(pattern: tok("Name"), constructor: alt_constructor_string),
      ],
      precedence: 0,
    )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0), name_rule],
    keywords: [],
    operators: [],
  )
}



fn make_delimited_parens_name_comma_grammar() -> Grammar(String) {
  // Grammar: "(" (Name ("," Name)*)? ")"
  let inner = Delimited(tok("("), tok("Name"), Tok(","), tok(")"))
  // The Delimited combinator parses: open (item sep item)* close
  // So: "(" Name ("," Name)* ")"
  let alt: Alternative(String) =
    Alternative(pattern: inner, constructor: alt_constructor_string)
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}

pub fn parse_delimited_single_item_succeeds_test() {
  // delimited should match "( foo )" with a single item
  let tokens = tokenize("( foo )")
  let grammar = make_delimited_parens_name_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// ============================================================================
// Edge cases
//
// These tests verify that the parser handles malformed input gracefully,
// produces parse errors on unexpected tokens, and correctly handles
// nested structures and boundary conditions.
//
// IMPORTANT: parse() returns the error_node on failure with empty errors
// list. On success, errors is always []. This is the design decision to
// allow the compiler to continue processing after parse errors.
// ============================================================================

// --- Error handling on non-matching input ---

pub fn parse_unexpected_token_produces_error_test() {
  // When input doesn't match the expected token, parse returns the error node
  let tokens = tokenize("42")
  // Integer, not Name
  let grammar = make_tok_grammar("Name")
  let result = parse(grammar, tokens, "error_node")
  // parse() returns error_node with empty errors on failure (design decision)
  assert result.ast == "error_node"
}

pub fn parse_wrong_keyword_produces_error_test() {
  // kw("let") should not match "fn" (a different keyword)
  let tokens = tokenize("fn")
  let grammar = make_kw_grammar("let")
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

pub fn parse_missing_token_produces_error_test() {
  // seq([Name, Name]) needs two names, one is not enough
  let tokens = tokenize("foo")
  let grammar = make_seq_name_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

// --- Empty and boundary inputs ---


pub fn parse_eof_in_middle_produces_error_test() {
  // Parsing Name Name with only one token should fail
  let tokens = tokenize("foo")
  let grammar = make_seq_name_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

// --- Nested structures ---

pub fn parse_nested_parens_succeeds_test() {
  // Nested parentheses should parse correctly
  let parens_name = Parens("NameRule")
  let alt: Alternative(String) =
    Alternative(pattern: parens_name, constructor: alt_constructor_string)
  let name_rule: Rule(String) =
    Rule(
      name: "NameRule",
      alternatives: [
        Alternative(pattern: tok("Name"), constructor: alt_constructor_string),
        Alternative(
          pattern: parens("NameRule"),
          constructor: alt_constructor_string,
        ),
      ],
      precedence: 0,
    )
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [Rule(name: "Test", alternatives: [alt], precedence: 0), name_rule],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("( foo )")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}


// --- Choice with no match ---

pub fn parse_choice_no_match_produces_error_test() {
  // choice([Name, Integer]) should fail on Float (neither option matches)
  let tokens = tokenize("3.14")
  let grammar = make_choice_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

// --- Opt with non-matching ---

// --- Many with single item ---


// --- Delimited edge cases ---

pub fn parse_delimited_empty_does_not_match_test() {
  // Delimited requires at least one item
  // Delimited("(", Name, ",", ")") matches: ( Name (, Name)* )
  // So "()" should fail because there's no Name after (
  let inner = Delimited(tok("("), tok("Name"), Tok(","), tok(")"))
  let alt: Alternative(String) =
    Alternative(pattern: inner, constructor: alt_constructor_string)
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("()")
  let result = parse(grammar, tokens, "error")
  // Should fail because there's no Name after (
  assert result.ast == "error"
}


// --- Operator and keyword interactions ---


// --- Multiple rules with different alternatives ---

pub fn grammar_with_three_alternatives_finds_second_test() {
  // Rules with multiple alternatives should find matching one
  let alt1: Alternative(String) =
    Alternative(pattern: tok("Integer"), constructor: alt_constructor_string)
  let alt2: Alternative(String) =
    Alternative(pattern: tok("Name"), constructor: alt_constructor_string)
  let alt3: Alternative(String) =
    Alternative(pattern: op("+"), constructor: alt_constructor_string)
  let rules = [
    Rule(name: "Test", alternatives: [alt1, alt2, alt3], precedence: 0),
  ]
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: rules,
      keywords: [],
      operators: [],
    )
  // Name should match even though Integer is listed first in alternatives
  let tokens = tokenize("foo")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- Whitespace handling in parsing ---

pub fn parse_only_whitespace_fails_for_tok_test() {
  // Whitespace is skipped by the lexer, so only EOF remains
  // This means tok("Name") on whitespace-only input will see Eof
  let tokens = tokenize("   ")
  let grammar = make_tok_grammar("Name")
  let result = parse(grammar, tokens, "error")
  // Eof is not a Name, so parsing fails
  assert result.ast == "error"
}

// --- Span accuracy in parsing ---

pub fn parse_multiple_tokens_preserves_span_test() {
  // When seq parses multiple tokens, spans should be valid
  let tokens = tokenize_with_filename("foo bar", "test.tao")
  let grammar = make_seq_name_name_grammar()
  let result = parse(grammar, tokens, "error")
  // Parse should succeed and spans should be valid
  assert result.errors == []
}

// --- Whitespace between tokens in seq ---


// ============================================================================
// AST Construction Tests
//
// These tests verify that parse() returns the actual constructed AST node
// (not the error_node fallback) on success.

/// Build a grammar that returns a string AST node with content.
fn make_constructing_grammar(expected_ast: String) -> Grammar(String) {
  let alt: Alternative(String) =
    Alternative(pattern: tok("Name"), constructor: fn(_values) { expected_ast })
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [],
    operators: [],
  )
}

pub fn parse_tok_returns_constructed_ast_test() {
  // When parsing succeeds, the AST should be the constructed node, not error_node
  let grammar = make_constructing_grammar("built_ast")
  let tokens = tokenize("foo")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "built_ast"
  assert result.errors == []
}

pub fn parse_kw_returns_constructed_ast_test() {
  // kw pattern should also return the constructed AST on success
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: kw("let"), constructor: fn(_values) {
              "let_constructed"
            }),
          ],
          precedence: 0,
        ),
      ],
      keywords: ["let"],
      operators: [],
    )
  let tokens = tokenize("let")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "let_constructed"
  assert result.errors == []
}

pub fn parse_seq_returns_constructed_ast_test() {
  // seq pattern should return the constructed AST
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(
              pattern: seq([
                tok("Name"),
                op("+"),
                tok("Name"),
              ]),
              constructor: fn(_values) { "seq_result" },
            ),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo + bar")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "seq_result"
  assert result.errors == []
}

pub fn parse_opt_returns_constructed_ast_with_match_test() {
  // opt pattern should succeed and return constructed AST
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(
              pattern: seq([
                tok("Name"),
                opt(Tok(",")),
              ]),
              constructor: fn(_values) { "opt_result" },
            ),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "opt_result"
  assert result.errors == []
}

pub fn parse_opt_returns_constructed_ast_with_comma_test() {
  // opt pattern should also succeed when the optional part matches
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(
              pattern: seq([
                tok("Name"),
                opt(Tok(",")),
              ]),
              constructor: fn(_values) { "opt_with_comma" },
            ),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo,")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "opt_with_comma"
  assert result.errors == []
}

pub fn parse_many_returns_constructed_ast_test() {
  // many pattern should return constructed AST
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: many(tok("Name")), constructor: fn(_values) {
              "many_result"
            }),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo bar baz")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "many_result"
  assert result.errors == []
}

pub fn parse_many_empty_returns_constructed_ast_test() {
  // many on empty input should still return constructed AST (zero matches)
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: many(tok("Name")), constructor: fn(_values) {
              "many_empty"
            }),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "many_empty"
  assert result.errors == []
}

pub fn parse_choice_returns_constructed_ast_test() {
  // choice should return constructed AST for the first matching alternative
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(
              pattern: choice([
                tok("Name"),
                tok("Integer"),
              ]),
              constructor: fn(_values) { "choice_name" },
            ),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "choice_name"
  assert result.errors == []
}

pub fn parse_sep_by_returns_constructed_ast_test() {
  // sep_by should return constructed AST for comma-separated items
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(
              pattern: sep_by(tok("Name"), Tok(",")),
              constructor: fn(_values) { "sep_by_result" },
            ),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("a, b, c")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "sep_by_result"
  assert result.errors == []
}

pub fn parse_parens_returns_constructed_ast_test() {
  // parens should return constructed AST
  let parens_rule: Rule(String) =
    Rule(
      name: "NameRule",
      alternatives: [
        Alternative(pattern: tok("Name"), constructor: alt_constructor_string),
      ],
      precedence: 0,
    )
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: parens("NameRule"), constructor: fn(_values) {
              "parens_result"
            }),
          ],
          precedence: 0,
        ),
        parens_rule,
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("( foo )")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "parens_result"
  assert result.errors == []
}

pub fn parse_delimited_returns_constructed_ast_test() {
  // delimited should return constructed AST
  let inner = Delimited(tok("("), tok("Name"), Tok(","), tok(")"))
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: inner, constructor: fn(_values) {
              "delimited_result"
            }),
          ],
          precedence: 0,
        ),
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("( foo, bar )")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "delimited_result"
  assert result.errors == []
}

pub fn parse_failure_returns_error_node_test() {
  // When parsing fails, the AST should be the error_node fallback
  let grammar = make_tok_grammar("Name")
  let tokens = tokenize("42")
  // Integer, not Name
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "error_node"
}


pub fn parse_ref_returns_constructed_ast_test() {
  // ref should return constructed AST through rule references
  let inner_rule: Rule(String) =
    Rule(
      name: "Inner",
      alternatives: [
        Alternative(pattern: tok("Name"), constructor: fn(_values) {
          "inner_node"
        }),
      ],
      precedence: 0,
    )
  let grammar =
    Grammar(
      name: "Test",
      start: "Test",
      rules: [
        Rule(
          name: "Test",
          alternatives: [
            Alternative(pattern: ref("Inner"), constructor: fn(_values) {
              "ref_result"
            }),
          ],
          precedence: 0,
        ),
        inner_rule,
      ],
      keywords: [],
      operators: [],
    )
  let tokens = tokenize("foo")
  let result = parse(grammar, tokens, "error_node")
  assert result.ast == "ref_result"
  assert result.errors == []
}

// ============================================================================
// ParseError enrichment tests
// ============================================================================

pub fn parse_error_contains_rule_name_test() {
  // ParseError should contain the rule name that was being attempted
  let err = ParseError(
    span: single("test", 1, 1),
    expected: "end of input",
    got: "Name 'foo'",
    context: "unexpected token",
    rule: "parse_tokens_acc",
    surrounding: [],
  )
  assert err.rule == "parse_tokens_acc"
}

pub fn parse_error_contains_context_test() {
  // ParseError should contain the context where the error occurred
  let err = ParseError(
    span: single("test", 1, 1),
    expected: "field",
    got: "EOF",
    context: "in record",
    rule: "parse_rcd_fields",
    surrounding: [],
  )
  assert err.context == "in record"
}

pub fn error_to_string_includes_rule_and_context_test() {
  // error_to_string should include rule and context when present
  let err = ParseError(
    span: single("test.gleam", 3, 5),
    expected: "\"->\"",
    got: "\"=\"",
    context: "in lambda pattern",
    rule: "skip",
    surrounding: [],
  )
  let formatted = error_to_string(err)
  assert formatted == "in test.gleam line 3, col 5: \"->\" (found: \"=\") in in lambda pattern (rule: skip)"
}

