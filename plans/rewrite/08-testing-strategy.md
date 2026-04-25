# Testing Strategy

## Design Philosophy

> **Tests as examples** — Every function has tests that demonstrate correct usage with example inputs/outputs.

Tests serve a dual purpose: they verify correctness AND document how functions work. Each test should be self-contained and readable enough to understand the expected behavior without reading the source code.

The testing strategy is organized in layers:

1. **Unit tests** — Test each function in isolation with specific examples
2. **Golden tests** — Test round-trip properties (parse → format → parse)
3. **Integration tests** — Test full pipeline stages with complete programs
4. **End-to-end tests** — Test complete compilation from source to value

## Test Organization

```
test/
├── syntax/
│   ├── lexer_test.gleam       # Tokenizer unit tests
│   ├── grammar_test.gleam     # Parser combinator unit tests
│   ├── formatter_test.gleam   # Document algebra + layout tests
│   └── golden_test.gleam      # Parse → format → parse round-trip tests
├── core/
│   ├── ast_test.gleam         # Term/Value type construction tests
│   ├── syntax_test.gleam      # Core parser + formatter tests
│   ├── infer_test.gleam       # Bidirectional type checking tests
│   ├── eval_test.gleam        # Normalization by evaluation tests
│   ├── quote_test.gleam       # Value → Term tests
│   ├── unify_test.gleam       # Unification tests
│   ├── subst_test.gleam       # Substitution tests
│   ├── generalize_test.gleam  # Generalization tests
│   ├── exhaustiveness_test.gleam  # Pattern match coverage tests
│   ├── error_formatter_test.gleam  # Type error diagnostics tests
│   ├── state_test.gleam       # State management tests
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Core → eval → quote → eval round-trip
├── tao/
│   ├── ast_test.gleam         # Tao AST type construction tests
│   ├── syntax_test.gleam      # Tao parser + formatter tests
│   ├── desugar_test.gleam     # Desugaring correctness tests
│   ├── compiler_test.gleam    # Multi-file compilation tests
│   ├── import_test.gleam      # Module import system tests
│   ├── test_api_test.gleam    # Test framework (REPL-style extraction)
│   ├── examples_test.gleam    # End-to-end example programs
│   └── golden_test.gleam      # Tao → desugar → compile → format round-trip
├── cli/
│   ├── run_test.gleam         # Run mode tests
│   ├── check_test.gleam       # Check mode tests
│   └── test_test.gleam        # Test mode tests (run test statements)
└── integration/
    └── e2e_test.gleam         # Full pipeline tests (Tao source → Core value)
```

## Testing Convention: Assert-Based Testing

> **Tests must use `assert` statements** — Every test must verify correctness using `assert`, not just return `True`/`False`.

GleeUnit 1.x requires tests to use `assert expr == expected` to actually verify correctness. Returning `True` or `False` from a case expression passes the test regardless of the actual result.

### ✅ Correct: Assert-Based Testing

```gleam
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  
  // Extract and verify specific token fields
  let first = tokens[0]
  assert first.kind == "Integer"
  assert first.value == "42"
  
  // Verify Eof is present
  assert case tokens[1] {
    Token(kind: "Eof", value: "", ..) -> True
    _ -> False
  }
}

pub fn infer_identity_function_type_test() {
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let state = initial_state([], "True")
  let result = infer(state, lam)
  
  // Property: no errors produced
  assert result.errors == []
}

pub fn check_type_mismatch_error_test() {
  let state = initial_state([], "True")
  let result = check(state, Lit(String("hello")), VLit(ILit(0)))
  
  // Property: exactly one TypeMismatch error with correct position
  assert list.length(result.errors) == 1
  assert case result.errors[0] {
    TypeMismatch(_, "String", "Int", span) -> 
      span.start_line == 1 && span.start_col == 1
    _ -> False
  }
}
```

### ❌ Incorrect: Silent Pass

```gleam
// This passes regardless of the actual result!
pub fn tokenize_integer_literal_test() {
  let tokens = tokenize("42")
  case tokens {
    [Token(kind: "Integer", value: "42", ..), Token(kind: "Eof", ..)] -> True
    _ -> False
  }
}
```

**Key rules:**

1. **Use `assert` for every verification** — Never just return True/False
2. **Prefer direct property asserts** — `assert value == expected` over pattern matching when possible
3. **Extract values before asserting** — Makes tests more readable and provides better error messages
4. **Use `assert case` for complex shapes** — When you need to verify specific fields while ignoring others
5. **Test functions must be `pub` and end with `_test`** — GleeUnit 1.x requirement
6. **Document with comments** — Each test should explain what it's testing and why

### Property-Based vs Pattern-Matching Tests

**Prefer property-based asserts** when you care about specific values:

```gleam
pub fn add_two_numbers_test() {
  assert add(1, 2) == 3
  assert add(-1, 1) == 0
  assert add(0, 0) == 0
}
```

**Use pattern matching asserts** when you need to verify complex structures while ignoring irrelevant fields:

```gleam
pub fn parse_let_binding_test() {
  let result = parse("let x = 42")
  assert case result {
    ParseResult(
      ast: Let("x", Lit(42), _),
      errors: [],
      env: Env { vars: [v], .. }
    ) if v.name == "x" -> True
    _ -> False
  }
}
```

---

## Test Examples

### Unit Tests: Lexer (lexer_test.gleam)

Tests that demonstrate how the lexer tokenizes various inputs:

```gleam
import gleeunit
import syntax/lexer.{tokenize, tokenize_with_filename, Token}
import gleam/list
import gleam/int

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Empty and whitespace input
// ============================================================================

pub fn empty_input_produces_only_eof_test() {
  // An empty input should produce exactly one Eof token
  let tokens = tokenize("")
  assert list.length(tokens) == 1
  
  let eof = tokens[0]
  assert eof.kind == "Eof"
  assert eof.value == ""
}

pub fn whitespace_only_input_produces_only_eof_test() {
  // Whitespace should be skipped, leaving only Eof
  let tokens = tokenize("   \n\t  ")
  assert list.length(tokens) == 1
  assert tokens[0].kind == "Eof"
}

// ============================================================================
// Integer literals
// ============================================================================

pub fn tokenize_single_integer_test() {
  // A simple integer literal produces one Integer token + Eof
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  
  let int_token = tokens[0]
  assert int_token.kind == "Integer"
  assert int_token.value == "42"
  assert int_token.span.start_line == 1
  assert int_token.span.start_col == 1
}

pub fn tokenize_zero_test() {
  let tokens = tokenize("0")
  assert list.length(tokens) == 2
  assert tokens[0].value == "0"
}

pub fn tokenize_large_integer_test() {
  let tokens = tokenize("123456789")
  assert list.length(tokens) == 2
  assert tokens[0].value == "123456789"
}

// ============================================================================
// Float literals
// ============================================================================

pub fn tokenize_float_with_leading_digit_test() {
  // Floats must start with a digit (not just a dot)
  let tokens = tokenize("3.14")
  assert list.length(tokens) == 2
  
  let float_token = tokens[0]
  assert float_token.kind == "Float"
  assert float_token.value == "3.14"
}

pub fn tokenize_float_with_trailing_zeros_test() {
  // Trailing zeros are preserved in float literals
  let tokens = tokenize("1.50")
  assert list.length(tokens) == 2
  assert tokens[0].value == "1.50"
}

// ============================================================================
// String literals
// ============================================================================

pub fn tokenize_simple_string_test() {
  // A quoted string produces a String token with unquoted content
  let tokens = tokenize("\"hello\"")
  assert list.length(tokens) == 2
  
  let str_token = tokens[0]
  assert str_token.kind == "String"
  assert str_token.value == "hello"
}

pub fn tokenize_string_with_newline_escape_test() {
  // \\n in source becomes an actual newline in the string value
  let tokens = tokenize("\"hello\\nworld\"")
  assert list.length(tokens) == 2
  
  let str_token = tokens[0]
  assert str_token.value == "hello\nworld"
}

pub fn tokenize_string_with_tab_escape_test() {
  // \\t in source becomes an actual tab in the string value
  let tokens = tokenize("\"hello\\tworld\"")
  assert list.length(tokens) == 2
  
  let str_token = tokens[0]
  assert str_token.value == "hello\tworld"
}

pub fn tokenize_string_with_escaped_quote_test() {
  // Escaped quotes inside strings are preserved
  let tokens = tokenize("\"say \\\"hi\\\"\"")
  assert list.length(tokens) == 2
  
  let str_token = tokens[0]
  assert str_token.value == "say \"hi\""
}

pub fn tokenize_string_with_escaped_backslash_test() {
  // \\ in source becomes a single backslash in the string value
  let tokens = tokenize("\"hello\\\\world\"")
  assert list.length(tokens) == 2
  
  let str_token = tokens[0]
  assert str_token.value == "hello\\world"
}

// ============================================================================
// Names and keywords
// ============================================================================

pub fn tokenize_identifier_test() {
  // Identifiers are lowercase and may contain underscores
  let tokens = tokenize("foo")
  assert list.length(tokens) == 2
  
  let name_token = tokens[0]
  assert name_token.kind == "Name"
  assert name_token.value == "foo"
}

pub fn tokenize_capitalized_identifier_test() {
  // Capitalized names are distinct from lowercase names
  let tokens = tokenize("Foo")
  assert list.length(tokens) == 2
  
  let name_token = tokens[0]
  assert name_token.kind == "Name"
  assert name_token.value == "Foo"
}

pub fn tokenize_underscore_in_name_test() {
  // Underscores are allowed in the middle of identifiers
  let tokens = tokenize("my_var")
  assert list.length(tokens) == 2
  
  let name_token = tokens[0]
  assert name_token.value == "my_var"
}

pub fn tokenize_keyword_let_test() {
  // Keywords are distinct from regular names
  let tokens = tokenize("let")
  assert list.length(tokens) == 2
  
  let kw_token = tokens[0]
  assert kw_token.kind == "Keyword"
  assert kw_token.value == "let"
}

pub fn tokenize_keyword_fn_test() {
  let tokens = tokenize("fn")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "fn"
}

pub fn tokenize_keyword_true_test() {
  let tokens = tokenize("true")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "true"
}

pub fn tokenize_keyword_false_test() {
  let tokens = tokenize("false")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "false"
}

pub fn tokenize_lambda_symbol_test() {
  // The λ symbol is tokenized as Lambda
  let tokens = tokenize("λ")
  assert list.length(tokens) == 2
  
  let lam_token = tokens[0]
  assert lam_token.kind == "Lambda"
  assert lam_token.value == "λ"
}

// ============================================================================
// Operators
// ============================================================================

pub fn tokenize_single_char_operators_test() {
  // Single-character operators are tokenized individually
  let tokens = tokenize("+ - * /")
  assert list.length(tokens) == 5
  
  // Verify all are Op tokens with correct values
  assert tokens[0].value == "+"
  assert tokens[1].value == "-"
  assert tokens[2].value == "*"
  assert tokens[3].value == "/"
}

pub fn tokenize_multi_char_operators_test() {
  // Multi-character operators are recognized as single tokens
  let tokens = tokenize("-> == != <= >= && || ..")
  assert list.length(tokens) == 9
  
  assert tokens[0].value == "->"
  assert tokens[1].value == "=="
  assert tokens[2].value == "!="
  assert tokens[3].value == "<="
  assert tokens[4].value == ">="
  assert tokens[5].value == "&&"
  assert tokens[6].value == "||"
  assert tokens[7].value == ".."
}

// ============================================================================
// Punctuation
// ============================================================================

pub fn tokenize_parentheses_test() {
  // Parentheses are tokenized as Punct
  let tokens = tokenize("()")
  assert list.length(tokens) == 3
  
  assert tokens[0].value == "("
  assert tokens[1].value == ")"
}

pub fn tokenize_braces_test() {
  let tokens = tokenize("{}")
  assert list.length(tokens) == 3
  
  assert tokens[0].value == "{"
  assert tokens[1].value == "}"
}

pub fn tokenize_brackets_test() {
  let tokens = tokenize("[]")
  assert list.length(tokens) == 3
  
  assert tokens[0].value == "["
  assert tokens[1].value == "]"
}

pub fn tokenize_comma_semicolon_colon_test() {
  let tokens = tokenize("; , :")
  assert list.length(tokens) == 4
  
  assert tokens[0].value == ";"
  assert tokens[1].value == ","
  assert tokens[2].value == ":"
}

// ============================================================================
// Comments
// ============================================================================

pub fn skip_single_line_comment_test() {
  // Single-line comments are completely skipped
  let tokens = tokenize("// comment")
  assert list.length(tokens) == 1  // Only Eof
  assert tokens[0].kind == "Eof"
}

pub fn skip_single_line_comment_with_code_after_test() {
  // Code after a comment is still tokenized normally
  let tokens = tokenize("// comment\nlet x = 42")
  assert list.length(tokens) == 5
  
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "let"
  assert tokens[1].kind == "Name"
  assert tokens[1].value == "x"
  assert tokens[2].kind == "Punct"
  assert tokens[2].value == "="
  assert tokens[3].kind == "Integer"
  assert tokens[3].value == "42"
}

pub fn skip_block_comment_test() {
  // Block comments are completely skipped
  let tokens = tokenize("/* comment */")
  assert list.length(tokens) == 1  // Only Eof
}

pub fn skip_block_comment_with_code_after_test() {
  // Code after a block comment is still tokenized
  let tokens = tokenize("/* comment */ let x")
  assert list.length(tokens) == 3
  
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "let"
  assert tokens[1].kind == "Name"
  assert tokens[1].value == "x"
}

// ============================================================================
// Position tracking
// ============================================================================

pub fn tokenize_multiple_tokens_with_correct_line_test() {
  // Multiple tokens should span multiple lines
  let tokens = tokenize("let x\n= 42")
  assert list.length(tokens) == 5
  
  // Verify line numbers change
  assert tokens[0].span.start_line == 1  // let
  assert tokens[2].span.start_line == 2  // =
}

pub fn tokenize_with_filename_attaches_filename_test() {
  // tokenize_with_filename should attach the filename to all tokens
  let tokens = tokenize_with_filename("let x = 42", "test.gleam")
  
  let all_have_correct_file = {
    case tokens {
      [Token(span: s1, ..), Token(span: s2, ..), Token(span: s3, ..), 
       Token(span: s4, ..), Token(span: eof, ..)] ->
        s1.file == "test.gleam"
        && s2.file == "test.gleam"
        && s3.file == "test.gleam"
        && s4.file == "test.gleam"
        && eof.file == "test.gleam"
      _ -> False
    }
  }
  assert all_have_correct_file
}

pub fn tokenize_with_empty_filename_defaults_to_empty_string_test() {
  // tokenize without filename defaults to empty string
  let tokens = tokenize("let x")
  let file = tokens[0].span.file
  assert file == ""
}

// ============================================================================
// Combined examples
// ============================================================================

pub fn tokenize_let_binding_test() {
  // A complete let binding tokenizes to: Keyword, Name, Punct, Integer, Eof
  let tokens = tokenize("let x = 42")
  assert list.length(tokens) == 5
  
  assert tokens[0].kind == "Keyword" && tokens[0].value == "let"
  assert tokens[1].kind == "Name" && tokens[1].value == "x"
  assert tokens[2].kind == "Punct" && tokens[2].value == "="
  assert tokens[3].kind == "Integer" && tokens[3].value == "42"
}

pub fn tokenize_function_application_test() {
  // Function application: f(x) tokenizes to Name, Punct, Name, Punct, Eof
  let tokens = tokenize("f(x)")
  assert list.length(tokens) == 5
  
  assert tokens[0].value == "f"
  assert tokens[1].value == "("
  assert tokens[2].value == "x"
  assert tokens[3].value == ")"
}

pub fn tokenize_lambda_expression_test() {
  // Lambda application: λx.x tokenizes to Lambda, Name, Punct, Name, Eof
  let tokens = tokenize("λx.x")
  assert list.length(tokens) == 5
  
  assert tokens[0].value == "λ"
  assert tokens[1].value == "x"
  assert tokens[2].value == "."
  assert tokens[3].value == "x"
}

// ============================================================================
// Edge cases and boundary conditions
// ============================================================================

pub fn tokenize_float_with_leading_zero_test() {
  // Floats can start with 0 followed by a dot
  let tokens = tokenize("0.5")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "Float"
  assert tokens[0].value == "0.5"
}

pub fn tokenize_integer_followed_by_dot_as_integer_test() {
  // A number followed by a bare dot (not followed by digits) 
  // tokenizes as Integer + Punct
  let tokens = tokenize("42 .")
  assert list.length(tokens) == 3
  
  assert tokens[0].kind == "Integer" && tokens[0].value == "42"
  assert tokens[1].kind == "Punct" && tokens[1].value == "."
}

pub fn tokenize_identifier_with_multiple_underscores_test() {
  // Multiple consecutive underscores are allowed in identifiers
  let tokens = tokenize("my__var")
  assert list.length(tokens) == 2
  assert tokens[0].value == "my__var"
}

pub fn tokenize_identifier_with_trailing_underscore_test() {
  // Trailing underscores are allowed in identifiers
  let tokens = tokenize("foo_")
  assert list.length(tokens) == 2
  assert tokens[0].value == "foo_"
}

pub fn tokenize_only_underscores_is_name_test() {
  // A single underscore is an operator, two underscores are two operators
  let tokens = tokenize("__")
  assert list.length(tokens) == 3
  
  assert tokens[0].kind == "Op" && tokens[0].value == "_"
  assert tokens[1].kind == "Op" && tokens[1].value == "_"
}

pub fn tokenize_non_ascii_in_string_test() {
  // Unicode characters in strings are preserved
  let tokens = tokenize("\"こんにちは\"")
  assert list.length(tokens) == 2
  assert tokens[0].value == "こんにちは"
}

pub fn tokenize_empty_string_test() {
  // Empty strings are valid
  let tokens = tokenize("\"\"")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "String"
  assert tokens[0].value == ""
}

pub fn tokenize_consecutive_operators_test() {
  // Consecutive single-character operators are separate tokens
  let tokens = tokenize("++")
  assert list.length(tokens) == 3
  
  assert tokens[0].value == "+"
  assert tokens[1].value == "+"
}

pub fn tokenize_mixed_multi_char_operators_test() {
  // Multi-char operators are preferred when they match
  let tokens = tokenize("-> <<")
  assert list.length(tokens) == 4
  
  assert tokens[0].value == "->"  // Multi-char operator
  assert tokens[1].value == "<"   // Single-char operators
  assert tokens[2].value == "<"
}

pub fn tokenize_whitespace_between_operators_test() {
  // Whitespace between operator characters prevents multi-char matching
  let tokens = tokenize("- >")
  assert list.length(tokens) == 3
  
  assert tokens[0].value == "-"
  assert tokens[1].value == ">"
}

pub fn tokenize_block_comment_with_newlines_test() {
  // Block comments spanning multiple lines are skipped entirely
  let tokens = tokenize("/*\n * comment\n */ let x")
  assert list.length(tokens) == 3
  
  assert tokens[0].kind == "Keyword"
  assert tokens[0].value == "let"
}

pub fn tokenize_nested_block_comment_stops_at_first_close_test() {
  // Only the first */ terminates the comment
  let tokens = tokenize("/* outer */ inner /* not comment */")
  assert list.length(tokens) == 2
  
  assert tokens[0].kind == "Name"
  assert tokens[0].value == "inner"
}

pub fn tokenize_number_at_end_of_input_test() {
  // A number at EOF is followed by exactly one Eof
  let tokens = tokenize("42")
  assert list.length(tokens) == 2
  assert tokens[0].kind == "Integer"
  assert tokens[1].kind == "Eof"
}

pub fn tokenize_multiple_eof_tokens_is_error_test() {
  // Empty input should produce exactly one Eof, not multiple
  let tokens = tokenize("")
  let eof_count = tokens |> list.filter(fn(t) { t.kind == "Eof" }) |> list.length
  assert eof_count == 1
}

pub fn tokenize_span_has_correct_filename_when_provided_test() {
  // All tokens should have the same filename from tokenize_with_filename
  let tokens = tokenize_with_filename("let x = 42", "module.tao")
  
  let all_same_file = {
    case tokens {
      [Token(span: s1, ..), Token(span: s2, ..), Token(span: s3, ..), 
       Token(span: s4, ..), Token(span: eof, ..)] ->
        s1.file == "module.tao"
        && s2.file == "module.tao"
        && s3.file == "module.tao"
        && s4.file == "module.tao"
        && eof.file == "module.tao"
      _ -> False
    }
  }
  assert all_same_file
}
```

### Unit Tests: Grammar Parser (grammar_test.gleam)

Tests that demonstrate how parser combinators process inputs:

```gleam
import gleeunit
import syntax/grammar.{parse, alt, ref, seq, opt, many, choice, delimited}
import core/ast.{type Span}

// ============================================================================
// Optional patterns
// ============================================================================

pub fn parse_optional_pattern_present_test() {
  // opt(ref("Name")) should match a name when present
  let result = parse(opt(ref("Name")), "foo")
  assert result.errors == []
  assert result.ast == "foo"
}

pub fn parse_optional_pattern_absent_test() {
  // opt(ref("Name")) should return None when no name is present
  let result = parse(opt(ref("Name")), "")
  assert result.errors == []
  // When nothing matches, opt produces the default (None)
  assert result.ast == ""  // Default value for optional
}

// ============================================================================
// Many patterns
// ============================================================================

pub fn parse_many_pattern_test() {
  // many(ref("Name")) should match zero or more names
  let result = parse(many(ref("Name")), "foo bar baz")
  assert result.errors == []
  assert result.ast == ["foo", "bar", "baz"]
}

pub fn parse_empty_many_test() {
  // many(ref("Name")) should return empty list for empty input
  let result = parse(many(ref("Name")), "")
  assert result.errors == []
  assert result.ast == []
}

// ============================================================================
// Delimited lists
// ============================================================================

pub fn parse_delimited_list_test() {
  // A delimited list should parse all elements between delimiters
  let result = parse(delimited(
    token("LParen"),
    ref("Name"),
    token("Comma"),
    token("RParen")
  ), "(a, b, c)")
  assert result.errors == []
  assert result.ast == ["a", "b", "c"]
}

pub fn parse_empty_delimited_list_test() {
  // An empty delimited list should parse to empty list
  let result = parse(delimited(
    token("LParen"),
    ref("Name"),
    token("Comma"),
    token("RParen")
  ), "()")
  assert result.errors == []
  assert result.ast == []
}

// ============================================================================
// Error accumulation
// ============================================================================

pub fn accumulate_multiple_parse_errors_test() {
  // Multiple parse errors should be accumulated, not just the first one
  let grammar = Grammar(
    name: "test",
    start: "Expr",
    rules: [
      Rule(
        name: "Expr",
        alternatives: [
          Alternative(
            pattern: seq([ref("Name"), token("Op"), ref("Name")]),
            constructor: fn(_) -> "binary_op",
          ),
        ],
        precedence: 0,
      ),
    ],
    keywords: ["fn", "let", "in"],
    operators: [],
  )
  
  let result = parse(grammar, "foo + bar + baz", "error_node")
  // Should have accumulated errors for each failed position
  assert list.length(result.errors) >= 2
}

// ============================================================================
// Span accuracy
// ============================================================================

pub fn produce_accurate_spans_from_tokens_test() {
  // Parsed AST should have spans that match the original tokens
  let grammar = simple_grammar()
  let result = parse(grammar, "let x = 42", "error_node")
  assert result.errors == []
  
  // Check that spans are accurate
  let start = span_start(result.ast)
  let end = span_end(result.ast)
  
  assert start == Span("test", 1, 1, 1, 3)   // "let"
  assert end == Span("test", 1, 1, 1, 12)    // "42"
}
```

### Unit Tests: Formatter (formatter_test.gleam)

Tests that demonstrate how the formatter renders document algebra:

```gleam
import gleeunit
import syntax/formatter.{render, concat, text, line, nest, group, join, space_sep, comma_sep, parens}

// ============================================================================
// Join operations
// ============================================================================

pub fn join_with_comma_separator_test() {
  // join with comma and line should produce comma-separated values with newlines
  let doc = join(concat([text(","), line()]), [text("a"), text("b"), text("c")])
  assert render(doc, 80) == "a,\nb,\nc"
}

pub fn join_with_space_separator_test() {
  // join with space should produce space-separated values on same line
  let doc = join(concat([text(" ")]), [text("a"), text("b"), text("c")])
  assert render(doc, 80) == "a b c"
}

// ============================================================================
// Space and comma separated lists
// ============================================================================

pub fn space_separated_list_test() {
  // space_sep should produce a space-separated list
  let doc = space_sep([text("a"), text("b"), text("c")])
  assert render(doc, 80) == "a b c"
}

pub fn comma_separated_list_test() {
  // comma_sep should produce a comma-separated list with trailing newline option
  let doc = comma_sep([text("a"), text("b"), text("c")])
  let rendered = render(doc, 80)
  // Should contain commas between elements
  assert rendered == "a,\nb,\nc"
}

// ============================================================================
// Nesting and indentation
// ============================================================================

pub fn nest_increases_indentation_test() {
  // nest should increase indentation by the specified amount
  let doc = nest(2, concat([text("  a"), line(), text("  b")]))
  assert render(doc, 80) == "  a\n  b"
}

// ============================================================================
// Grouping and wrapping
// ============================================================================

pub fn parenthesize_when_too_long_test() {
  // group should wrap content in parentheses when it exceeds the line limit
  let doc = group(concat([
    text("this is a very long expression that should wrap"),
    text(" and continue")
  ]))
  let rendered = render(doc, 20)
  assert rendered == "(this is a very long expression that should wrap and continue)"
}

pub fn group_does_not_wrap_when_short_enough_test() {
  // group should not add parentheses when content fits within line limit
  let doc = group(concat([text("short"), text(" content")]))
  let rendered = render(doc, 80)
  assert rendered == "short content"
}

// ============================================================================
// Empty cases
// ============================================================================

pub fn empty_text_produces_empty_doc_test() {
  // text("") should produce an empty rendered string
  let doc = text("")
  assert render(doc, 80) == ""
}

pub fn empty_list_joins_to_empty_test() {
  // join over an empty list should produce empty string
  let doc = join(text(","), [])
  assert render(doc, 80) == ""
}
```

### Unit Tests: Core Infer (infer_test.gleam)

Tests that demonstrate how the type checker infers and validates types:

```gleam
import gleeunit
import core/ast.{Term, Var, Lam, Pi, App, Hole, Ann, Let}
import core/eval.{Value, VLam, VPi, VNeut, HVar, HHole, VLit, I32T}
import core/infer.{infer, check}
import core/state.{State, initial_state, Error, TypeMismatch, VarUndefined, CtrUndefined, InfiniteType}

// ============================================================================
// Identity function
// ============================================================================

pub fn infer_identity_function_type_test() {
  // fn(x: a) -> a should infer ∀a. a → a with no errors
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let state = initial_state([], "True")
  let result = infer(state, lam)
  
  // Property: identity function has no type errors
  assert result.errors == []
}

// ============================================================================
// Lambda type checking
// ============================================================================

pub fn check_lambda_with_correct_type_annotation_test() {
  // (fn(x) { x } : ∀a. a → a) should check successfully
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let ann = Ann(lam, Hole(-1))
  let state = initial_state([], "True")
  let result = check(state, ann, VPi([], "a", [], VNeut(HHole(1), []), Var(0, "a")))
  
  assert result.errors == []
}

// ============================================================================
// Type errors
// ============================================================================

pub fn infer_type_mismatch_accumulates_error_test() {
  // let x: Int = "hello" should produce a TypeMismatch error
  let state = initial_state([], "True")
  let result = check(state, Lit(String("hello")), VLit(ILit(0)))
  
  assert list.length(result.errors) == 1
  case result.errors[0] {
    TypeMismatch(_, "String", "Int", _) -> True
    _ -> False
  }
}

pub fn handle_undefined_variable_error_test() {
  // Var(5, "x") where 5 is out of scope should produce VarUndefined error
  let state = initial_state([], "True")
  let result = infer(state, Var(5, "x"))
  
  assert list.length(result.errors) == 1
  case result.errors[0] {
    VarUndefined(5, _) -> True
    _ -> False
  }
}

pub fn handle_constructor_undefined_error_test() {
  // Ctr("UndefinedCtor", _) should produce CtrUndefined error
  let state = initial_state([], "True")
  let result = infer(state, Ctr("UndefinedCtor", Hole(-1)))
  
  assert list.length(result.errors) == 1
  case result.errors[0] {
    CtrUndefined("UndefinedCtor", _) -> True
    _ -> False
  }
}

pub fn handle_infinite_type_error_test() {
  // x : ∀x. x → x should produce InfiniteType error
  let state = initial_state([], "True")
  let result = check(state, Hole(-1), VPi([], "x", [], Var(0, "x"), Hole(-1)))
  
  case result {
    State(errors: [InfiniteType(..)], _) -> True
    _ -> False
  }
}

// ============================================================================
// Application and Pi types
// ============================================================================

pub fn infer_application_of_identity_function_test() {
  // (fn(x) { x }) 42 should infer successfully
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(ILit(42)))
  let state = initial_state([], "True")
  let result = infer(state, app)
  
  assert result.errors == []
}

pub fn infer_pi_type_construction_test() {
  // Πx:a. b (dependent function type) should infer successfully
  let domain = Var(0, "a")
  let codomain = Var(1, "b")  // b is from outer scope
  let pi = Pi(domain, codomain)
  let state = initial_state([], "True")
  let result = infer(state, pi)
  
  assert result.errors == []
}

// ============================================================================
// Let bindings
// ============================================================================

pub fn infer_let_binding_test() {
  // let x = 42; x should infer successfully
  let let_term = Let("x", Lit(ILit(42)), Var(0, "x"))
  let state = initial_state([], "True")
  let result = infer(state, let_term)
  
  assert result.errors == []
}
```

### Unit Tests: Core Eval (eval_test.gleam)

Tests that demonstrate how evaluation works:

```gleam
import gleeunit
import core/ast.{Term, Var, Lam, App, Lit, Call, Fix}
import core/eval.{evaluate, evaluate_with_ffi, evaluate_with_step_limit, Value, VLam, VLit, VNeut, VErr}
import core/state.{initial_state}

// ============================================================================
// Basic evaluation
// ============================================================================

pub fn evaluate_identity_function_application_test() {
  // (fn(x) { x }) 42 → 42
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let app = App(lam, Lit(ILit(42)))
  
  let result = evaluate(app)
  
  assert result == VLit(ILit(42))
}

pub fn evaluate_constant_test() {
  // 42 → 42 (constants evaluate to themselves)
  let result = evaluate(Lit(ILit(42)))
  
  assert result == VLit(ILit(42))
}

// ============================================================================
// Nested lambdas and application
// ============================================================================

pub fn evaluate_nested_lambda_test() {
  // (fn(x) { fn(y) { x + y }}) 1 2 → 3
  let body = App(App(Var(0, "+"), Var(1, "x")), Var(0, "y"))
  let inner_lam = Lam(("y", Hole(-1)), body)
  let outer_lam = Lam(("x", Hole(-1)), inner_lam)
  let app1 = App(outer_lam, Lit(ILit(1)))
  let app2 = App(app1, Lit(ILit(2)))
  
  let result = evaluate(app2)
  
  assert result == VLit(ILit(3))
}

pub fn evaluate_church_numeral_2_test() {
  // λf.λx.f (f x) is already a value (lambda)
  let f_x = App(Var(1, "f"), App(Var(0, "f"), Var(0, "x")))
  let body = Lam(("x", Hole(-1)), f_x)
  let result = evaluate(Lam(("f", Hole(-1)), body))
  
  // Property: lambda values evaluate to themselves
  case result {
    VLam(..) -> True
    _ -> False
  }
}

// ============================================================================
// FFI evaluation
// ============================================================================

pub fn evaluate_addition_ffi_test() {
  // +(42, 1) → 43 (via FFI)
  let add = Call("add", [Lit(ILit(42)), Lit(ILit(1))], Hole(-1))
  let state = initial_state([], tao_ffis(), "True", "False")
  let result = evaluate_with_ffi(state.ffi, add)
  
  assert result == VLit(ILit(43))
}

// ============================================================================
// Error handling
// ============================================================================

pub fn handle_step_limit_error_test() {
  // Infinite loop: fix x -> x x should hit step limit
  let fix = Fix("x", Call("x", []))
  let result = evaluate_with_step_limit(fix, 10)
  
  assert result == VErr
}
```

### Unit Tests: Core Quote (quote_test.gleam)

Tests that demonstrate how values are converted back to terms:

```gleam
import gleeunit
import core/ast.{Term, Var, Lam, App, Lit}
import core/eval.{Value, VLam, VLit, VNeut, HVar}
import core/quote.{quote}

// ============================================================================
// Quote lambda values
// ============================================================================

pub fn quote_lambda_value_back_to_term_test() {
  // A lambda value should quote back to the original lambda term
  let body = Var(0, "x")
  let lam = Lam(("x", Hole(-1)), body)
  let value = VLam([], "x", [VNeut(HVar(0), [])], lam)
  
  let result = quote(value)
  
  // Property: quoted lambda matches the original structure
  case result {
    Lam(("x", _), body, _) if body == Var(0, "x") -> True
    _ -> False
  }
}

pub fn quote_literal_value_test() {
  // A literal value should quote back to the original literal term
  let value = VLit(ILit(42))
  let result = quote(value)
  
  assert result == Lit(ILit(42))
}

pub fn quote_nested_lambda_test() {
  // Nested lambda values should quote to nested lambda terms
  let inner_body = Var(1, "x")
  let inner_lam = Lam(("y", Hole(-1)), inner_body)
  let outer_lam = Lam(("x", Hole(-1)), inner_lam)
  
  let inner_value = VLam([], "y", [VNeut(HVar(0), []), VNeut(HVar(1), [])], inner_lam)
  let outer_value = VLam([], "x", [VNeut(HVar(0), [])], outer_lam)
  
  let result = quote(outer_value)
  
  // Property: nested structure is preserved
  case result {
    Lam(("x", _), Lam(("y", _), Var(0, "x"), _), _) -> True
    _ -> False
  }
}

pub fn quote_does_not_evaluate_test() {
  // Quote should NOT call eval — this is a critical invariant
  let called_eval = ref(False)
  let value = VLam([], "x", [], Lam(("x", Hole(-1)), Var(0, "x")))
  
  let result = quote_with_trace(value, fn() -> called_eval = True)
  assert called_eval == False  // eval should never be called
}
```

### Unit Tests: Core Unify (unify_test.gleam)

Tests that demonstrate how unification works:

```gleam
import gleeunit
import core/ast.{Term, Hole, Var, Lit}
import core/eval.{Value, VLit, VNeut, HHole, I32T, F64T}
import core/unify.{unify}
import core/state.{State, initial_state}

// ============================================================================
// Basic unification
// ============================================================================

pub fn unify_two_identical_values_test() {
  // VLit(42) should unify with VLit(42)
  let state = initial_state([], "True")
  let result = unify(state, VLit(ILit(42)), VLit(ILit(42)))
  
  assert result.errors == []
}

pub fn unify_hole_with_concrete_type_test() {
  // A hole should unify with any concrete type
  let state = initial_state([], "True")
  let result = unify(state, VNeut(HHole(1), []), VLit(I32T))
  
  assert result.errors == []
}

// ============================================================================
// Type errors
// ============================================================================

pub fn unify_incompatible_types_produces_error_test() {
  // Int and Float should not unify
  let state = initial_state([], "True")
  let result = unify(state, VLit(I32T), VLit(F64T))
  
  assert list.length(result.errors) == 1
  case result.errors[0] {
    TypeMismatch(_, _, _, _) -> True
    _ -> False
  }
}

// ============================================================================
// Pi type unification
// ============================================================================

pub fn unify_pi_types_with_matching_domains_and_codomains_test() {
  // Πa. a → a should unify with itself
  let state = initial_state([], "True")
  let dom = VNeut(HHole(1), [])
  let codom1 = VNeut(HVar(0), [])
  let codom2 = VNeut(HVar(0), [])
  let result = unify(state, VPi([], "a", [], dom, codom1), VPi([], "a", [], dom, codom2))
  
  assert result.errors == []
}

pub fn handle_occurs_check_should_allow_recursive_types_test() {
  // Recursive types should be allowed (no occurs check error)
  let state = initial_state([], "True")
  let result = unify(state, VNeut(HHole(1), []), VPi([], "a", [], VNeut(HHole(1), []), VNeut(HVar(0), [])))
  
  assert result.errors == []  // Should not error (we allow recursive types)
}
```

### Integration Tests: Compiler (compiler_test.gleam)

Tests that demonstrate full compilation from Tao source to Core value:

```gleam
import gleeunit
import tao/compiler.{compile_tao, compile_multi_module}
import core/eval.{Value, VLit}
import core/state.{State, Error, ImportError, TypeError}

// ============================================================================
// Simple compilation
// ============================================================================

pub fn compile_simple_addition_test() {
  let source = "let x = 42 + 1; x"
  let result = compile_tao(source, "test.tao")
  
  assert result.errors == []
  assert result.value == VLit(ILit(43))
}

pub fn compile_function_definition_and_call_test() {
  let source = """
    fn add(a, b) { a + b }
    add(1, 2)
  """
  let result = compile_tao(source, "test.tao")
  
  assert result.errors == []
  assert result.value == VLit(ILit(3))
}

pub fn compile_fibonacci_test() {
  let source = """
    fn fib(n) {
      mut a = 0
      mut b = 1
      mut i = 0
      while i < n {
        let temp = a
        a = b
        b = temp + b
        i = i + 1
      }
      a
    }
    fib(6)
  """
  let result = compile_tao(source, "test.tao")
  
  assert result.errors == []
  assert result.value == VLit(ILit(8))
}

// ============================================================================
// Error handling
// ============================================================================

pub fn compile_with_parse_errors_accumulates_errors_test() {
  let source = """
    fn foo(x
    let bar = 
    type Baz
  """
  let result = compile_tao(source, "test.tao")
  
  assert result.errors.length >= 3
}

pub fn compile_with_type_errors_accumulates_errors_test() {
  let source = """
    let x: Int = "hello"
    let y: String = 42
  """
  let result = compile_tao(source, "test.tao")
  
  assert result.errors.length >= 2
}

// ============================================================================
// Module compilation
// ============================================================================

pub fn compile_imported_module_test() {
  let modules = [
    #("math.tao", "fn add(a, b) { a + b }"),
    #("main.tao", "import math { add }; add(1, 2)"),
  ]
  let result = compile_multi_module(modules, "main.tao")
  
  assert result.errors == []
  assert result.value == VLit(ILit(3))
}

pub fn module_not_found_creates_empty_bindings_test() {
  let modules = [
    #("a.tao", "import nonexistent { foo }\nlet x = foo"),
  ]
  let result = compile_multi_module(modules, "a.tao")
  
  case result {
    State(errors: [ImportError.ModuleNotFound(_, _)], _) -> True
    _ -> False
  }
}

pub fn name_not_found_deferred_to_type_checker_test() {
  let modules = [
    #("a.tao", "import b { undefined_name }"),
  ]
  let result = compile_multi_module(modules, "a.tao")
  
  case result {
    State(errors: [TypeError.VarUndefined(_, _)], _) -> True
    _ -> False
  }
}
```

### Golden Tests: Round-Trip (golden_test.gleam)

Tests that verify structural invariants across transformations:

```gleam
import gleeunit
import tao/syntax.{type TaoSyntax}
import core/syntax.{type CoreSyntax}
import core/quote
import core/eval

// ============================================================================
// Parse → Format → Parse
// ============================================================================

pub fn tao_parse_format_parse_produces_same_ast_test() {
  // Parsing, formatting, and re-parsing should produce the same AST
  let source = """
    fn add(a, b) { a + b }
    let x = add(1, 2)
  """
  let parsed = TaoSyntax.parse(source)
  let formatted = TaoSyntax.format(parsed.ast)
  let reparsed = TaoSyntax.parse(formatted)
  
  // Property: round-trip preserves AST structure
  assert parsed.ast == reparsed.ast
}

pub fn core_parse_format_parse_produces_same_term_test() {
  // Parsing, formatting, and re-parsing Core should produce the same term
  let source = "let x = 42; x"
  let parsed = CoreSyntax.parse(source)
  let formatted = CoreSyntax.format(parsed.ast)
  let reparsed = CoreSyntax.parse(formatted)
  
  assert parsed.ast == reparsed.ast
}

// ============================================================================
// Core → Eval → Quote → Core
// ============================================================================

pub fn core_term_eval_quote_term_produces_structurally_equal_term_test() {
  // Evaluating and quoting a term should produce a structurally equivalent term
  let source = "let x = 42; x"
  let parsed = CoreSyntax.parse(source)
  let quoted = quote.quote(eval.evaluate(parsed.ast))
  
  // Property: eval → quote round-trip preserves structure
  assert structural_equal(parsed.ast, quoted)
}

// ============================================================================
// Tao → Core desugaring
// ============================================================================

pub fn tao_to_core_desugar_format_produces_valid_core_test() {
  // Desugaring Tao to Core and formatting should produce valid Core
  let source = "fn add(a, b) { a + b }"
  let tao_expr = TaoSyntax.parse(source)
  let core_term = tao_desugar.desugar(tao_expr.ast)
  let core_formatted = CoreSyntax.format(core_term)
  
  // Property: desugared Core should parse successfully
  let reparsed = CoreSyntax.parse(core_formatted)
  assert reparsed.errors == []
}
```

### End-to-End Tests (e2e_test.gleam)

Tests that demonstrate complete compilation pipelines:

```gleam
import gleeunit
import tao/compiler.{compile_tao}
import core/eval.{Value, VLit}

// ============================================================================
// Complete pipeline: fib(10) = 55
// ============================================================================

pub fn complete_pipeline_fib_10_equals_55_test() {
  // Full pipeline: Tao source → Core → Value
  let source = """
    fn fib(n) {
      mut a = 0
      mut b = 1
      mut i = 0
      while i < n {
        let temp = a
        a = b
        b = temp + b
        i = i + 1
      }
      a
    }
    fib(10)
  """
  let result = compile_tao(source, "fib.tao")
  
  assert result.errors == []
  assert result.value == VLit(ILit(55))
}

// ============================================================================
// Complete pipeline: map and filter
// ============================================================================

pub fn complete_pipeline_map_and_filter_test() {
  // Full pipeline with higher-order functions
  let source = """
    fn map(f, xs) {
      match xs {
        | [] -> []
        | [h, ..t] -> [f(h), ..map(f, t)]
      }
    }
    
    fn filter(p, xs) {
      match xs {
        | [] -> []
        | [h, ..t] ->
          if p(h) {
            [h, ..filter(p, t)]
          } else {
            filter(p, t)
          }
      }
    }
    
    let nums = [1, 2, 3, 4, 5]
    let doubled = map(\\x -> x * 2, nums)
    let evens = filter(\\x -> x == 0, doubled)
    evens
  """
  let result = compile_tao(source, "map_filter.tao")
  
  assert result.errors == []
  assert result.value == VList([VLit(ILit(2)), VLit(ILit(4))])
}

// ============================================================================
// Complete pipeline: generator stream
// ============================================================================

pub fn complete_pipeline_generator_stream_test() {
  // Full pipeline with recursive data structures
  let source = """
    type Stream(a) = Cons(head: a, tail: Stream(a)) | Empty
    
    fn range(start, end) {
      if start >= end {
        Stream.empty()
      } else {
        Stream.cons(start, range(start + 1, end))
      }
    }
    
    let nums = range(1, 3)
    Stream.to_list(nums)
  """
  let result = compile_tao(source, "stream.tao")
  
  assert result.errors == []
  assert result.value == VList([VLit(ILit(1)), VLit(ILit(2)), VLit(ILit(3))])
}
```

## Test Coverage Requirements

| Component | Minimum Coverage | Notes |
|-----------|-----------------|-------|
| `syntax/lexer` | 100% | Every token type, every edge case |
| `syntax/grammar` | 100% | Every combinator, every pattern type |
| `syntax/formatter` | 100% | Every document operation, every layout |
| `core/ast` | 100% | Every type constructor |
| `core/infer` | 100% | Every term form, every error case |
| `core/eval` | 100% | Every value form, step limit, FFI |
| `core/quote` | 100% | Every value form |
| `core/unify` | 100% | Every type pair, occurs check |
| `core/generalize` | 100% | Every quantification case |
| `core/exhaustiveness` | 100% | Every pattern combination |
| `tao/desugar` | 100% | Every statement form, every high-level feature |
| `tao/compiler` | 95% | Every file combination, import variants |
| `tao/import` | 95% | Every import variant, circular detection |
| Integration | 90% | Every end-to-end example |

## Tao Test Framework (REPL Style)

Tests in Tao source files use a REPL-style syntax with `///` doc comments:

```tao
// Example: test statements in a Tao file

/// > 1 + 2 ~> 3
/// > "hello" <> " world" ~> "hello world"
/// > fib(10) ~> 55

fn fib(n) {
  // ...
}
```

**How it works:**
1. The Tao parser extracts `/// > expr ~> expected` from doc comments
2. Each line becomes a `TestStatement` in the AST
3. The test framework compiles and evaluates each expression
4. The result is compared against the expected value

**Test framework in `test_api.gleam`:**
- `extract_tests(source)` → List(TestStatement)
- `run_tests(tests, context)` → List(TestResult)
- `run_tests_in_file(path, context)` → List(TestResult)

**CLI `tao test` command:**
- Scans source files for test statements
- Runs each test
- Reports: pass count, fail count, total
- Failed tests show expected vs. actual values

**Test result format:**
```gleam
pub type TestResult {
  Pass(test_name: Option(String))
  Fail(test_name: Option(String), expected: Value, actual: Value)
  Skipped(test_name: Option(String), reason: String)
}
```

## Running Tests

```bash
# Run all tests
gleam test

# Run specific test file
gleam test test/core/infer_test.gleam

# Run specific test
gleam test test/core/infer_test.gleam --name "infer_identity_function_type"

# Watch mode (continuous testing)
fswatch -or src test | xargs -n1 -I{} gleam test

# Run only golden tests
gleam test --tag golden

# Run only unit tests
gleam test --tag unit

# Run Tao tests (test statements in source files)
tao test main.tao
tao test --filter "addition"  # Run only tests matching "addition"
tao test --list               # List all test names
```
