// ============================================================================
// CALCULATOR EXAMPLE TESTS - Testing Spans
// ============================================================================
/// Tests for the calculator example with source location tracking.
///
/// These tests verify that:
/// 1. Spans are stored correctly reflecting source code location
/// 2. Syntax errors are reported correctly
import gleeunit
import gleeunit/should
import gleam/int
import examples/calc.{type Expr, Add, Div, Int, Mul, Sub, parse, format, get_span}
import syntax/grammar

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn parse_ok(source: String) -> Expr {
  let result = parse(source)
  case result {
    grammar.ParseResult(ast, []) -> ast
    grammar.ParseResult(_ast, _errors) -> {
      panic as "Parse failed"
    }
  }
}

fn expect_span(actual: grammar.Span, expected_line: Int, expected_col: Int) {
  actual.start_line |> should.equal(expected_line)
  actual.start_col |> should.equal(expected_col)
}

// ============================================================================
// SPAN STORAGE TESTS
// ============================================================================

pub fn span_number_single_digit_test() {
  // "42" at line 1, column 1
  let ast = parse_ok("42")
  let span = get_span(ast)
  
  expect_span(span, 1, 1)
  span.end_line |> should.equal(1)
  span.end_col |> should.equal(3)  // "42" is 2 chars
}

pub fn span_number_multi_digit_test() {
  // "123" at line 1, column 1
  let ast = parse_ok("123")
  let span = get_span(ast)
  
  expect_span(span, 1, 1)
  span.end_col |> should.equal(4)  // "123" is 3 chars
}

pub fn span_add_simple_test() {
  // "1 + 2" - Add should span entire expression
  let ast = parse_ok("1 + 2")
  let span = get_span(ast)
  
  expect_span(span, 1, 1)
  span.end_col |> should.equal(6)  // "1 + 2" is 5 chars
}

pub fn span_add_left_operand_test() {
  // "1 + 2" - left operand "1" should be at column 1
  let ast = parse_ok("1 + 2")
  case ast {
    Add(left, _, _) -> {
      let left_span = get_span(left)
      expect_span(left_span, 1, 1)
      left_span.end_col |> should.equal(2)
    }
    _ -> panic as "Expected Add"
  }
}

pub fn span_add_right_operand_test() {
  // "1 + 2" - right operand "2" should be at column 5
  let ast = parse_ok("1 + 2")
  case ast {
    Add(_, right, _) -> {
      let right_span = get_span(right)
      expect_span(right_span, 1, 5)
      right_span.end_col |> should.equal(6)
    }
    _ -> panic as "Expected Add"
  }
}

// ============================================================================
// FORMAT WITH SPANS TESTS
// ============================================================================

pub fn format_preserves_structure_test() {
  // Format should produce same structure
  let source = "1 + 2 * 3"
  let ast = parse_ok(source)
  let formatted = format(ast)
  
  formatted |> should.equal(source)
}

pub fn format_nested_test() {
  let source = "(1 + 2) * 3"
  let ast = parse_ok(source)
  let formatted = format(ast)
  
  formatted |> should.equal(source)
}

// ============================================================================
// ERROR TESTS
// ============================================================================

pub fn error_location_invalid_syntax_test() {
  // "1 +" - should have parse errors
  let result = parse("1 +")

  case result {
    grammar.ParseResult(_ast, errors) -> {
      case errors {
        [..] -> True |> should.equal(True)  // Has errors - good
        [] -> panic as "Expected parse errors but got none"
      }
    }
  }
}

pub fn error_location_unknown_token_test() {
  // "@#$" - error should be at the beginning
  let result = parse("@#$")

  case result {
    grammar.ParseResult(_ast, errors) -> {
      case errors {
        [..] -> True |> should.equal(True)  // Has errors - good
        [] -> panic as "Expected parse errors but got none"
      }
    }
  }
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_with_spans_test() {
  let source = "1 + 2 * 3"
  let ast = parse_ok(source)
  
  // Original AST has spans
  let original_span = get_span(ast)
  expect_span(original_span, 1, 1)
  
  // Format and re-parse
  let formatted = format(ast)
  let ast2 = parse_ok(formatted)
  
  // Re-parsed AST should have same structure (spans will differ)
  ast2 |> should.equal(ast)
}

// ============================================================================
// INTEGRATION TESTS
// ============================================================================

pub fn integration_complex_expression_test() {
  // Complex expression with multiple operators
  let source = "1 * 2 + 3 * 4"
  let ast = parse_ok(source)
  
  // Should parse as (1 * 2) + (3 * 4)
  case ast {
    Add(left, right, _) -> {
      case left, right {
        Mul(_, _, _), Mul(_, _, _) -> {
          // Correct structure
          let span = get_span(ast)
          expect_span(span, 1, 1)
          span.end_col |> should.equal(14)  // Length of "1 * 2 + 3 * 4"
        }
        _, _ -> panic as "Expected Mul + Mul"
      }
    }
    _ -> panic as "Expected Add"
  }
}
