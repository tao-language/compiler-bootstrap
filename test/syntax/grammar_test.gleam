// ============================================================================
// GRAMMAR TESTS
// ============================================================================
/// Tests for the syntax/grammar module.
///
/// Tests grammar pattern helpers including delimited lists.
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{
  type Grammar, type ParseResult, type Value,
  parse,
  alt, token_pattern, ref, rule, many, delimited,
  AstValue, ListValue, TokenValue, Grammar,
}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Create a test grammar for delimited list parsing
fn delimited_grammar(item_rule: String) -> Grammar(List(String)) {
  Grammar(
    name: "Test",
    start: "Program",
    rules: [
      rule("Program", [
        alt(
          delimited(
            token_pattern("LParen"),
            ref(item_rule),
            token_pattern("Comma"),
            token_pattern("RParen"),
          ),
          fn(values) { extract_values(values) },
        ),
      ]),
      rule(item_rule, [
        alt(token_pattern("Number"), fn(values) {
          case values {
            [TokenValue(t)] -> [t.value]
            _ -> []
          }
        }),
        alt(token_pattern("Ident"), fn(values) {
          case values {
            [TokenValue(t)] -> [t.value]
            _ -> []
          }
        }),
      ]),
    ],
    tokens: ["LParen", "RParen", "Comma", "Number", "Ident"],
    keywords: [],
    operators: [],
  )
}

/// Parse and extract values
fn parse_delimited(source: String) -> Result(List(String), List(String)) {
  let grammar = delimited_grammar("Primary")
  let result = parse(grammar, source, [])
  case result.errors {
    [] -> Ok(result.ast)
    errors -> {
      let error_msgs = list.map(errors, fn(e) { e.expected })
      Error(error_msgs)
    }
  }
}

/// Extract string values from parsed AST
fn extract_values(values: List(Value(List(String)))) -> List(String) {
  list.flat_map(values, fn(v) {
    case v {
      AstValue(items) -> items
      ListValue(vs) -> extract_values(vs)
      _ -> []
    }
  })
}

// ============================================================================
// DELIMITED LIST TESTS
// ============================================================================

pub fn delimited_empty_test() {
  // Test empty list: ()
  parse_delimited("()") |> should.equal(Ok([]))
}

pub fn delimited_single_item_test() {
  // Test single item: (1)
  parse_delimited("(1)") |> should.equal(Ok(["1"]))
}

pub fn delimited_two_items_test() {
  // Test two items: (1, 2)
  parse_delimited("(1, 2)") |> should.equal(Ok(["1", "2"]))
}

pub fn delimited_three_items_test() {
  // Test three items: (1, 2, 3)
  parse_delimited("(1, 2, 3)") |> should.equal(Ok(["1", "2", "3"]))
}

pub fn delimited_trailing_separator_test() {
  // Test trailing separator: (1, 2, 3,)
  parse_delimited("(1, 2, 3,)") |> should.equal(Ok(["1", "2", "3"]))
}

pub fn delimited_with_identifiers_test() {
  // Test with identifiers: (x, y, z)
  parse_delimited("(x, y, z)") |> should.equal(Ok(["x", "y", "z"]))
}

pub fn delimited_mixed_test() {
  // Test mixed numbers and identifiers: (1, x, 2, y)
  parse_delimited("(1, x, 2, y)") |> should.equal(Ok(["1", "x", "2", "y"]))
}

pub fn delimited_with_spaces_test() {
  // Test with various spacing: ( 1 , 2 , 3 )
  parse_delimited("( 1 , 2 , 3 )") |> should.equal(Ok(["1", "2", "3"]))
}

pub fn delimited_no_separator_fails_test() {
  // Test missing separator should fail: (1 2)
  case parse_delimited("(1 2)") {
    Ok(_) -> {
      panic as "Should have failed to parse list without separator"
    }
    Error(_) -> {
      // Expected - parse error, test passes
      True |> should.be_true
    }
  }
}

pub fn delimited_unclosed_fails_test() {
  // Test unclosed list should fail: (1, 2
  case parse_delimited("(1, 2") {
    Ok(_) -> {
      panic as "Should have failed to parse unclosed list"
    }
    Error(_) -> {
      // Expected - parse error, test passes
      True |> should.be_true
    }
  }
}
