// ============================================================================
// CORE SYNTAX TESTS
// ============================================================================

import core/syntax
import gleeunit
import gleeunit/should
import parser

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

fn round_trip(source: String) -> Result(String, List(parser.ParseError)) {
  let result = syntax.parse(source)
  case result.errors {
    [] -> Ok(syntax.format(result.ast))
    errors -> Error(errors)
  }
}

fn expect_parse_error(
  result: parser.ParseResult(parser.Tree),
  expected_message: String,
  expected_row: Int,
  expected_col: Int,
) {
  case result.errors {
    [] -> panic as "Expected error but got none"
    [error, ..] -> {
      error.message |> should.equal(expected_message)
      error.location.start.row |> should.equal(expected_row)
      error.location.start.col |> should.equal(expected_col)
    }
  }
}

// ============================================================================
// BASIC PARSING TESTS
// ============================================================================

pub fn parse_ident_test() {
  let result = syntax.parse("x")
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Ident", "x", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Ident leaf"
  }
}

pub fn parse_number_test() {
  let result = syntax.parse("42")
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Number", "42", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Number leaf"
  }
}

pub fn parse_string_test() {
  let result = syntax.parse("\"hello\"")
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("String", "hello", _, _)) -> True |> should.be_true
    _ -> panic as "Expected String leaf"
  }
}

// ============================================================================
// FUNCTION EXPRESSION TESTS
// ============================================================================

pub fn parse_fn_simple_test() {
  let result = syntax.parse("fn(x, y) -> x")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_fn_empty_test() {
  let result = syntax.parse("fn() -> 42")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// MATCH EXPRESSION TESTS
// ============================================================================

pub fn parse_match_simple_test() {
  let result = syntax.parse("match x { | A -> a | B -> b }")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_match_single_case_test() {
  let result = syntax.parse("match x { | A -> a }")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// LET EXPRESSION TESTS
// ============================================================================

pub fn parse_let_simple_test() {
  let result = syntax.parse("let x -> 42")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_let_with_expr_test() {
  let result = syntax.parse("let x -> fn() -> 42")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// DO EXPRESSION TESTS
// ============================================================================

pub fn parse_do_simple_test() {
  let result = syntax.parse("do ReadLine()")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// HANDLE EXPRESSION TESTS
// ============================================================================

pub fn parse_handle_simple_test() {
  let result = syntax.parse("handle comp { | return(x) -> x }")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_handle_multiple_test() {
  let result = syntax.parse("handle comp { | return(x) -> x | return(y) -> y }")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// APPLICATION TESTS
// ============================================================================

pub fn parse_app_simple_test() {
  let result = syntax.parse("f(x)")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_app_multiple_args_test() {
  let result = syntax.parse("add(1, 2)")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn parse_app_no_args_test() {
  let result = syntax.parse("f()")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// ROUND TRIP TESTS
// ============================================================================

pub fn round_trip_ident_test() {
  let source = "x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Ident", "x", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Ident leaf"
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn round_trip_number_test() {
  let source = "42"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Number", "42", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Number leaf"
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn round_trip_fn_test() {
  let source = "fn(x, y) -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn round_trip_match_test() {
  let source = "match x { | A -> a }"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn round_trip_let_test() {
  let source = "let x -> 42"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn round_trip_app_test() {
  let source = "f(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

// ============================================================================
// ERROR RECOVERY TESTS
// ============================================================================

pub fn error_recovery_produces_valid_ast_test() {
  let result = syntax.parse("let x -> 42")
  result.errors |> should.equal([])
  case result.ast {
    parser.Empty -> panic as "Expected non-empty AST"
    _ -> True |> should.be_true
  }
}

pub fn error_recovery_handles_incomplete_input_test() {
  let result = syntax.parse("f")
  result.errors |> should.equal([])
  case result.ast {
    parser.Leaf(parser.Token("Ident", "f", _, _)) -> True |> should.be_true
    _ -> panic as "Expected Ident leaf"
  }
}
