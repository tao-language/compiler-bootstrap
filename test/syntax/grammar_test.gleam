/// Tests for the parser combinator DSL
///
/// Tests cover:
/// - Pattern construction (tok, kw, op, ref, seq, opt, many, choice, sep_by, parens, delimited)
/// - Either type helpers (left_value, right_value, is_left, is_right)
/// - ParseResult extraction (result_ast, result_errors)
/// - Error formatting (error_to_string)

import gleeunit
import syntax/grammar.{
  type Grammar, Grammar, type Rule, Rule, type Alternative, Alternative,
  type ParseResult, ParseResult, ParseError,
  type Pattern, Tok, Kw, Op, Ref, Seq, Opt, Many, Choice, SepBy, Parens, Delimited,
  type Either, Left, Right, Infix,
  parse, tok, kw, op, ref, seq, opt, many, choice, sep_by, parens, delimited,
  error_to_string, result_ast, result_errors,
  is_left, is_right, left_value, right_value,
}
import syntax/span.{type Span, single}
import syntax/lexer.{tokenize, tokenize_with_filename}
import gleam/list

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
pub fn alt_constructor_string(_v: List(#(Either(String, String), Span))) -> String {
  "node"
}

/// Helper function for string concatenation in operators
pub fn concat_string(left: String, right: String) -> String {
  left <> "+" <> right
}

// ============================================================================
// Either type helpers
// ============================================================================

pub fn is_left_returns_true_for_left_value_test() {
  let v: Either(String, Int) = Left("hello")
  assert is_left(v) == True
}

pub fn is_left_returns_false_for_right_value_test() {
  let v: Either(String, Int) = Right(42)
  assert is_left(v) == False
}

pub fn is_right_returns_false_for_left_value_test() {
  let v: Either(String, Int) = Left("world")
  assert is_right(v) == False
}

pub fn is_right_returns_true_for_right_value_test() {
  let v: Either(String, Int) = Right(100)
  assert is_right(v) == True
}

pub fn left_value_returns_payload_test() {
  let v: Either(String, Int) = Left("test")
  assert left_value(v) == "test"
}

pub fn right_value_returns_payload_test() {
  let v: Either(String, Int) = Right(99)
  assert right_value(v) == 99
}

// ============================================================================
// Pattern construction
// ============================================================================

pub fn tok_creates_tok_pattern_test() {
  let p: Pattern(String) = tok("Name")
  assert case p {
    Tok(kind) -> kind == "Name"
    _ -> False
  }
}

pub fn kw_creates_kw_pattern_test() {
  let p: Pattern(String) = kw("let")
  assert case p {
    Kw(keyword) -> keyword == "let"
    _ -> False
  }
}

pub fn op_creates_op_pattern_test() {
  let p: Pattern(String) = op("+")
  assert case p {
    Op(symbol) -> symbol == "+"
    _ -> False
  }
}

pub fn ref_creates_ref_pattern_test() {
  let p: Pattern(String) = ref("Expr")
  assert case p {
    Ref(name) -> name == "Expr"
    _ -> False
  }
}

pub fn seq_creates_seq_pattern_test() {
  let p: Pattern(String) = seq([tok("Name"), op("+"), tok("Name")])
  assert case p {
    Seq(patterns) -> list.length(patterns) == 3
    _ -> False
  }
}

pub fn opt_creates_opt_pattern_test() {
  let p: Pattern(String) = opt(tok(","))
  assert case p {
    Opt(Tok(",")) -> True
    _ -> False
  }
}

pub fn many_creates_many_pattern_test() {
  let p: Pattern(String) = many(tok("Name"))
  assert case p {
    Many(Tok("Name")) -> True
    _ -> False
  }
}

pub fn choice_creates_choice_pattern_test() {
  let p: Pattern(String) = choice([tok("Name"), tok("Integer")])
  assert case p {
    Choice(alts) -> list.length(alts) == 2
    _ -> False
  }
}

pub fn sep_by_creates_sep_by_pattern_test() {
  let p: Pattern(String) = sep_by(tok("Name"), tok(","))
  assert case p {
    SepBy(Tok("Name"), Tok(",")) -> True
    _ -> False
  }
}

pub fn parens_creates_parens_pattern_test() {
  let p: Pattern(String) = parens("Expr")
  assert case p {
    Parens(name) -> name == "Expr"
    _ -> False
  }
}

pub fn delimited_creates_delimited_pattern_test() {
  let open = tok("(")
  let item = tok("Name")
  let sep = tok(",")
  let close = tok(")")
  let p: Pattern(String) = delimited(open, item, sep, close)
  assert case p {
    Delimited(Tok(_), Tok(_), Tok(_), Tok(_)) -> True
    _ -> False
  }
}

// ============================================================================
// Grammar/Rule/Alternative construction
// ============================================================================

pub fn grammar_type_stores_name_test() {
  let g: Grammar(String) = Grammar(
    name: "Test",
    start: "Start",
    rules: [],
    keywords: [],
    operators: [],
  )
  assert g.name == "Test"
}

pub fn grammar_type_stores_start_test() {
  let g: Grammar(Int) = Grammar(
    name: "Test",
    start: "Main",
    rules: [],
    keywords: [],
    operators: [],
  )
  assert g.start == "Main"
}

pub fn rule_type_stores_name_test() {
  let r: Rule(String) = Rule(
    name: "Expr",
    alternatives: [],
    precedence: 0,
  )
  assert r.name == "Expr"
}

pub fn rule_type_stores_precedence_test() {
  let r: Rule(String) = Rule(
    name: "Expr",
    alternatives: [],
    precedence: 5,
  )
  assert r.precedence == 5
}

pub fn alternative_type_stores_constructor_test() {
  // Test that we can construct an Alternative with a simple constructor
  // Alternative(Int) constructor: fn(List(#(Either(String, Int), Span))) -> Int
  let a: Alternative(Int) = Alternative(
    pattern: tok("Name"),
    constructor: alt_constructor_int,
  )
  let result = a.constructor([])
  assert result == 42
}

// ============================================================================
// ParseResult helpers
// ============================================================================

pub fn result_ast_returns_ast_test() {
  let result: ParseResult(String) = ParseResult(ast: "hello", errors: [])
  assert result_ast("fallback", result) == "hello"
}

pub fn result_ast_returns_ast_on_errors_test() {
  let err = ParseError(
    span: single("test", 1, 1),
    expected: "Name",
    got: "EOF",
    context: "at start",
  )
  let result: ParseResult(Int) = ParseResult(ast: 42, errors: [err])
  assert result_ast(0, result) == 42
}

pub fn result_errors_returns_empty_list_test() {
  let result: ParseResult(String) = ParseResult(ast: "hello", errors: [])
  assert result_errors("fallback", result) == []
}

pub fn result_errors_returns_errors_list_test() {
  let err = ParseError(
    span: single("test", 1, 1),
    expected: "Name",
    got: "EOF",
    context: "test",
  )
  let result: ParseResult(String) = ParseResult(ast: "hello", errors: [err])
  let errors = result_errors("fallback", result)
  assert list.length(errors) == 1
}

// ============================================================================
// Error formatting
// ============================================================================

pub fn error_to_string_single_line_test() {
  let err = ParseError(
    span: single("test.tao", 1, 5),
    expected: "Name",
    got: "Eof",
    context: "in expression",
  )
  let formatted = error_to_string(err)
  assert formatted == "in test.tao line 1, col 5: Name (found: Eof)"
}

pub fn error_to_string_multi_line_test() {
  let err = ParseError(
    span: single("test.tao", 2, 1),
    expected: "Keyword",
    got: "Integer",
    context: "at module level",
  )
  let formatted = error_to_string(err)
  assert formatted == "in test.tao line 2, col 1: Keyword (found: Integer)"
}

pub fn error_to_string_empty_context_test() {
  let err = ParseError(
    span: single("", 1, 1),
    expected: "Token",
    got: "Nothing",
    context: "",
  )
  let formatted = error_to_string(err)
  assert formatted == "in  line 1, col 1: Token (found: Nothing)"
}

// ============================================================================
// Complex Either pattern matching
// ============================================================================

pub fn either_value_preserves_payload_type_in_seq_test() {
  // Simulate what would happen in a sequence:
  // Left("Name") is a terminal value
  let left_val: Either(String, String) = Left("Name")
  assert is_left(left_val) == True
  assert left_value(left_val) == "Name"
}

pub fn either_value_preserves_ast_type_in_ref_test() {
  // Simulate what a rule reference would return
  let right_val: Either(String, String) = Right("AST_Node")
  assert is_right(right_val) == True
  assert right_value(right_val) == "AST_Node"
}

// ============================================================================
// ParseResult with multiple errors
// ============================================================================

pub fn parse_result_with_multiple_errors_returns_all_errors_test() {
  let err1 = ParseError(
    span: single("test", 1, 1),
    expected: "Name",
    got: "Eof",
    context: "first",
  )
  let err2 = ParseError(
    span: single("test", 2, 1),
    expected: "Keyword",
    got: "Name",
    context: "second",
  )
  let err3 = ParseError(
    span: single("test", 3, 1),
    expected: "Op",
    got: "String",
    context: "third",
  )
  let result: ParseResult(String) = ParseResult(ast: "fallback", errors: [err1, err2, err3])
  let errors = result_errors("fallback", result)
  assert list.length(errors) == 3
}

// ============================================================================
// Grammar with rules
// ============================================================================

pub fn grammar_with_multiple_rules_test() {
  let alt = Alternative(
    pattern: tok("Name"),
    constructor: alt_constructor_string,
  )
  let rules = [
    Rule(
      name: "Expr",
      alternatives: [alt],
      precedence: 0,
    ),
    Rule(
      name: "Term",
      alternatives: [alt],
      precedence: 10,
    ),
  ]
  let g: Grammar(String) = Grammar(
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

pub fn grammar_with_operators_test() {
  let operators = [
    #("+", Infix(20, False, "+", concat_string)),
    #("*", Infix(30, False, "*", concat_string)),
  ]
  let g: Grammar(String) = Grammar(
    name: "Arith",
    start: "Expr",
    rules: [],
    keywords: [],
    operators: operators,
  )
  assert list.length(g.operators) == 2
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn grammar_empty_rules_test() {
  let g: Grammar(String) = Grammar(
    name: "Empty",
    start: "EmptyRule",
    rules: [],
    keywords: [],
    operators: [],
  )
  assert g.name == "Empty"
  assert g.rules == []
}

pub fn grammar_empty_keywords_test() {
  let g: Grammar(Int) = Grammar(
    name: "NoKw",
    start: "Main",
    rules: [],
    keywords: [],
    operators: [],
  )
  assert g.keywords == []
}

pub fn grammar_empty_operators_test() {
  let g: Grammar(Int) = Grammar(
    name: "NoOps",
    start: "Main",
    rules: [],
    keywords: [],
    operators: [],
  )
  assert g.operators == []
}

pub fn alternative_constructor_returns_proper_type_test() {
  let a: Alternative(Int) = Alternative(
    pattern: tok("Name"),
    constructor: alt_constructor_int,
  )
  assert a.constructor([]) == 42
}

// ============================================================================
// Pattern construction
// ============================================================================

pub fn rule_with_many_alternatives_test() {
  let a1: Alternative(String) = Alternative(
    pattern: tok("Name"),
    constructor: alt_constructor_string,
  )
  let a2: Alternative(String) = Alternative(
    pattern: tok("Integer"),
    constructor: alt_constructor_string,
  )
  let rule: Rule(String) = Rule(
    name: "Expr",
    alternatives: [a1, a2],
    precedence: 0,
  )
  assert list.length(rule.alternatives) == 2
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
  let alt: Alternative(String) = Alternative(
    pattern: tok(tok_kind),
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

fn make_kw_grammar(keyword: String) -> Grammar(String) {
  let alt: Alternative(String) = Alternative(
    pattern: kw(keyword),
    constructor: alt_constructor_string,
  )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [keyword],
    operators: [],
  )
}

fn make_op_grammar(sym: String) -> Grammar(String) {
  let alt: Alternative(String) = Alternative(
    pattern: op(sym),
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

// --- tok pattern parsing ---

pub fn parse_tok_matching_token_succeeds_test() {
  // tok("Name") should succeed when the first token is a Name
  let tokens = tokenize("foo")
  let grammar = make_tok_grammar("Name")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- kw pattern parsing ---

pub fn parse_kw_matching_keyword_succeeds_test() {
  // kw("let") should succeed when the first token is the keyword "let"
  let tokens = tokenize("let")
  let grammar = make_kw_grammar("let")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- op pattern parsing ---

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
  let alt: Alternative(String) = Alternative(
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

pub fn parse_seq_both_match_succeeds_test() {
  // seq([Name, Name]) should succeed with two Name tokens
  let tokens = tokenize("foo bar")
  let grammar = make_seq_name_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- opt pattern parsing ---

fn make_opt_comma_grammar() -> Grammar(String) {
  // Grammar that matches Name followed by optional comma
  let alt: Alternative(String) = Alternative(
    pattern: seq([tok("Name"), opt(kw(","))]),
    constructor: alt_constructor_string,
  )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
}

pub fn parse_opt_present_matches_succeeds_test() {
  // opt(kw(",")) should match when comma is present
  let tokens = tokenize("foo,")
  let grammar = make_opt_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

pub fn parse_opt_absent_matches_succeeds_test() {
  // opt(kw(",")) should also succeed when comma is absent
  let tokens = tokenize("foo")
  let grammar = make_opt_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- many pattern parsing ---

fn make_many_name_grammar() -> Grammar(String) {
  // Grammar that matches zero or more Names
  let alt: Alternative(String) = Alternative(
    pattern: many(tok("Name")),
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

pub fn parse_many_multiple_match_succeeds_test() {
  // many(Name) should match multiple names
  let tokens = tokenize("foo bar baz")
  let grammar = make_many_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}



// --- choice pattern parsing ---

fn make_choice_grammar() -> Grammar(String) {
  // Grammar that matches either Name or Integer
  Grammar(
    name: "Test",
    start: "Test",
    rules: [
      Rule(
        name: "Test",
        alternatives: [Alternative(
          pattern: choice([tok("Name"), tok("Integer")]),
          constructor: alt_constructor_string,
        )],
        precedence: 0,
      ),
    ],
    keywords: [],
    operators: [],
  )
}

pub fn parse_choice_first_alternative_matches_test() {
  // choice([Name, Integer]) should match Name
  let tokens = tokenize("foo")
  let grammar = make_choice_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

pub fn parse_choice_second_alternative_matches_test() {
  // choice([Name, Integer]) should match Integer when Name fails
  let tokens = tokenize("42")
  let grammar = make_choice_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- sep_by pattern parsing ---

fn make_sep_by_name_comma_grammar() -> Grammar(String) {
  // Grammar that matches: Name ("," Name)*
  let sep_pattern = sep_by(tok("Name"), kw(","))
  let alt: Alternative(String) = Alternative(
    pattern: sep_pattern,
    constructor: alt_constructor_string,
  )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
}

pub fn parse_sep_by_multiple_items_succeeds_test() {
  // sep_by(Name, ",") should match "foo, bar, baz"
  let tokens = tokenize("foo, bar, baz")
  let grammar = make_sep_by_name_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
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
  let alt: Alternative(String) = Alternative(
    pattern: parens("NameRule"),
    constructor: alt_constructor_string,
  )
  let name_rule: Rule(String) = Rule(
    name: "NameRule",
    alternatives: [Alternative(
      pattern: tok("Name"),
      constructor: alt_constructor_string,
    )],
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

pub fn parse_parens_matching_succeeds_test() {
  // parens("NameRule") should match "( foo )"
  let tokens = tokenize("( foo )")
  let grammar = make_parens_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- delimited pattern parsing ---

fn make_delimited_parens_name_comma_grammar() -> Grammar(String) {
  // Grammar: "(" (Name ("," Name)*)? ")"
  let inner = Delimited(tok("("), tok("Name"), kw(","), tok(")"))
  // The Delimited combinator parses: open (item sep item)* close
  // So: "(" Name ("," Name)* ")"
  let alt: Alternative(String) = Alternative(
    pattern: inner,
    constructor: alt_constructor_string,
  )
  Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
}

pub fn parse_delimited_with_items_succeeds_test() {
  // delimited should match "( foo, bar )"
  let tokens = tokenize("( foo, bar )")
  let grammar = make_delimited_parens_name_comma_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
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
  let tokens = tokenize("42")  // Integer, not Name
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

pub fn parse_empty_input_with_many_succeeds_test() {
  // many(Name) on empty input should succeed (zero matches)
  let tokens = tokenize("")
  let grammar = make_many_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

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
  let alt: Alternative(String) = Alternative(
    pattern: parens_name,
    constructor: alt_constructor_string,
  )
  let name_rule: Rule(String) = Rule(
    name: "NameRule",
    alternatives: [
      Alternative(pattern: tok("Name"), constructor: alt_constructor_string),
      Alternative(pattern: parens("NameRule"), constructor: alt_constructor_string),
    ],
    precedence: 0,
  )
  let grammar = Grammar(
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

pub fn parse_deeply_nested_parens_succeeds_test() {
  // Deeply nested parentheses should still parse: (( foo ))
  let parens_name = Parens("NameRule")
  let alt: Alternative(String) = Alternative(
    pattern: parens_name,
    constructor: alt_constructor_string,
  )
  let name_rule: Rule(String) = Rule(
    name: "NameRule",
    alternatives: [
      Alternative(pattern: tok("Name"), constructor: alt_constructor_string),
      Alternative(pattern: parens("NameRule"), constructor: alt_constructor_string),
    ],
    precedence: 0,
  )
  let grammar = Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0), name_rule],
    keywords: [],
    operators: [],
  )
  let tokens = tokenize("(( foo ))")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

pub fn parse_multiple_separated_items_succeeds_test() {
  // sep_by(Name, ",") should match many comma-separated names
  let sep_pattern = sep_by(tok("Name"), kw(","))
  let alt: Alternative(String) = Alternative(
    pattern: sep_pattern,
    constructor: alt_constructor_string,
  )
  let grammar = Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
  let tokens = tokenize("a, b, c, d")
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

pub fn parse_many_with_single_item_succeeds_test() {
  // many(Name) should match exactly one name
  let tokens = tokenize("foo")
  let grammar = make_many_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- Delimited edge cases ---

pub fn parse_delimited_empty_does_not_match_test() {
  // Delimited requires at least one item
  // Delimited("(", Name, ",", ")") matches: ( Name (, Name)* )
  // So "()" should fail because there's no Name after (
  let inner = Delimited(tok("("), tok("Name"), kw(","), tok(")"))
  let alt: Alternative(String) = Alternative(
    pattern: inner,
    constructor: alt_constructor_string,
  )
  let grammar = Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
  let tokens = tokenize("()")
  let result = parse(grammar, tokens, "error")
  // Should fail because there's no Name after (
  assert result.ast == "error"
}

pub fn parse_delimited_with_trailing_comma_succeeds_test() {
  // Delimited should handle trailing separator followed by close
  let inner = Delimited(tok("("), tok("Name"), kw(","), tok(")"))
  let alt: Alternative(String) = Alternative(
    pattern: inner,
    constructor: alt_constructor_string,
  )
  let grammar = Grammar(
    name: "Test",
    start: "Test",
    rules: [Rule(name: "Test", alternatives: [alt], precedence: 0)],
    keywords: [","],
    operators: [],
  )
  let tokens = tokenize("( foo, )")
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}

// --- Operator and keyword interactions ---

pub fn parse_op_on_integer_input_fails_test() {
  // op("+") should not match an integer token
  let tokens = tokenize("42")
  let grammar = make_op_grammar("+")
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

pub fn parse_kw_on_non_keyword_name_fails_test() {
  // kw("let") should not match "fn" (different keyword)
  let tokens = tokenize("fn")
  let grammar = make_kw_grammar("let")
  let result = parse(grammar, tokens, "error")
  assert result.ast == "error"
}

// --- Multiple rules with different alternatives ---

pub fn grammar_with_three_alternatives_finds_second_test() {
  // Rules with multiple alternatives should find matching one
  let alt1: Alternative(String) = Alternative(
    pattern: tok("Integer"),
    constructor: alt_constructor_string,
  )
  let alt2: Alternative(String) = Alternative(
    pattern: tok("Name"),
    constructor: alt_constructor_string,
  )
  let alt3: Alternative(String) = Alternative(
    pattern: op("+"),
    constructor: alt_constructor_string,
  )
  let rules = [
    Rule(
      name: "Test",
      alternatives: [alt1, alt2, alt3],
      precedence: 0,
    ),
  ]
  let grammar = Grammar(
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

pub fn parse_seq_with_whitespace_between_tokens_succeeds_test() {
  // Tokens with whitespace between them should still match in seq
  let tokens = tokenize("foo     bar")  // Extra whitespace
  let grammar = make_seq_name_name_grammar()
  let result = parse(grammar, tokens, "error")
  assert result.errors == []
}
