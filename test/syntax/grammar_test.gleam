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
  tok, kw, op, ref, seq, opt, many, choice, sep_by, parens, delimited,
  error_to_string, result_ast, result_errors,
  is_left, is_right, left_value, right_value,
}
import syntax/span.{type Span, single}
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
    Opt(inner) -> case inner {
      Tok(kind) -> kind == ","
      _ -> False
    }
    _ -> False
  }
}

pub fn many_creates_many_pattern_test() {
  let p: Pattern(String) = many(tok("Name"))
  assert case p {
    Many(inner) -> case inner {
      Tok(kind) -> kind == "Name"
      _ -> False
    }
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
    SepBy(item, sep) -> case item {
      Tok(item_kind) -> case sep {
        Tok(sep_kind) -> item_kind == "Name" && sep_kind == ","
        _ -> False
      }
      _ -> False
    }
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
    Delimited(o, i, s, c) -> case o {
      Tok(_) -> case i {
        Tok(_) -> case s {
          Tok(_) -> case c {
            Tok(_) -> True
            _ -> False
          }
          _ -> False
        }
        _ -> False
      }
      _ -> False
    }
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
// Either type edge cases
// ============================================================================

pub fn is_left_works_with_string_left_test() {
  // The is_left/is_right functions in grammar.gleam are typed as Either(String, a)
  let left: Either(String, Int) = Left("hello")
  let right: Either(String, Int) = Right(42)
  assert is_left(left) == True
  assert is_right(right) == True
}

pub fn is_left_is_false_for_right_test() {
  let v: Either(String, Int) = Right(42)
  assert is_left(v) == False
  assert is_right(v) == True
}

pub fn is_right_is_false_for_left_test() {
  let v: Either(String, Int) = Left("world")
  assert is_left(v) == True
  assert is_right(v) == False
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
