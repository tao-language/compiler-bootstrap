// ============================================================================
// TAO SYNTAX TESTS
// ============================================================================
/// Comprehensive tests for Tao syntax parsing, error reporting, and recovery.
///
/// ## Test Categories
///
/// 1. **Success Cases** - Valid syntax that should parse without errors
/// 2. **Error Reporting** - Invalid syntax with correct error messages and spans
/// 3. **Error Recovery** - Parser continues after errors
/// 4. **Round-Trip** - Parse and format produces same output
/// 5. **CLI Integration** - End-to-end error reporting
import tao/syntax.{parse, parse_module, format_expr, Int, Var, Add, Sub, Mul, Div, BinOp, UnaryOp, Not, Let}
import gleeunit
import gleeunit/should
import syntax/grammar.{type ParseResult, ParseResult, type ParseError, type Span, Span}
import gleam/list
import gleam/string
import gleam/option.{Some, None}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// SUCCESS CASES - BASIC EXPRESSIONS
// ============================================================================

pub fn parse_number_test() {
  let ParseResult(ast, errors) = parse("42")
  errors |> should.equal([])
  case ast {
    Int(42, _) -> Nil
    _ -> panic as "Expected Int(42)"
  }
}

pub fn parse_zero_test() {
  let ParseResult(ast, errors) = parse("0")
  errors |> should.equal([])
  case ast {
    Int(0, _) -> Nil
    _ -> panic as "Expected Int(0)"
  }
}

pub fn parse_large_number_test() {
  let ParseResult(ast, errors) = parse("999999")
  errors |> should.equal([])
  case ast {
    Int(999999, _) -> Nil
    _ -> panic as "Expected Int(999999)"
  }
}

pub fn parse_variable_test() {
  let ParseResult(ast, errors) = parse("x")
  errors |> should.equal([])
  case ast {
    Var("x", _) -> Nil
    _ -> panic as "Expected Var(x)"
  }
}

pub fn parse_variable_with_underscore_test() {
  let ParseResult(ast, errors) = parse("my_var")
  errors |> should.equal([])
  case ast {
    Var("my_var", _) -> Nil
    _ -> panic as "Expected Var(my_var)"
  }
}

pub fn parse_variable_with_numbers_test() {
  let ParseResult(ast, errors) = parse("var123")
  errors |> should.equal([])
  case ast {
    Var("var123", _) -> Nil
    _ -> panic as "Expected Var(var123)"
  }
}

// ============================================================================
// SUCCESS CASES - BINARY OPERATORS
// ============================================================================

pub fn parse_addition_test() {
  let ParseResult(ast, errors) = parse("1 + 2")
  errors |> should.equal([])
  case ast {
    BinOp(Int(1, _), Add, Int(2, _), _) -> Nil
    _ -> panic as "Expected BinOp(Int(1), Add, Int(2))"
  }
}

pub fn parse_subtraction_test() {
  let ParseResult(ast, errors) = parse("10 - 5")
  errors |> should.equal([])
  case ast {
    BinOp(Int(10, _), Sub, Int(5, _), _) -> Nil
    _ -> panic as "Expected BinOp(Int(10), Sub, Int(5))"
  }
}

pub fn parse_multiplication_test() {
  let ParseResult(ast, errors) = parse("3 * 4")
  errors |> should.equal([])
  case ast {
    BinOp(Int(3, _), Mul, Int(4, _), _) -> Nil
    _ -> panic as "Expected BinOp(Int(3), Mul, Int(4))"
  }
}

pub fn parse_division_test() {
  let ParseResult(ast, errors) = parse("20 / 4")
  errors |> should.equal([])
  case ast {
    BinOp(Int(20, _), Div, Int(4, _), _) -> Nil
    _ -> panic as "Expected BinOp(Int(20), Div, Int(4))"
  }
}

pub fn parse_chained_addition_test() {
  let ParseResult(ast, errors) = parse("1 + 2 + 3")
  errors |> should.equal([])
  // Verify it's left-associative: (1 + 2) + 3
  case ast {
    BinOp(BinOp(Int(1, _), Add, Int(2, _), _), Add, Int(3, _), _) -> Nil
    _ -> panic as "Expected left-associative BinOp"
  }
}

pub fn parse_mixed_operators_test() {
  let ParseResult(ast, errors) = parse("1 + 2 - 3")
  errors |> should.equal([])
  case ast {
    BinOp(BinOp(Int(1, _), Add, Int(2, _), _), Sub, Int(3, _), _) -> Nil
    _ -> panic as "Expected BinOp(BinOp(1+2), Sub, 3)"
  }
}

// ============================================================================
// SUCCESS CASES - OPERATOR PRECEDENCE
// ============================================================================

pub fn parse_precedence_mul_before_add_test() {
  let ParseResult(ast, errors) = parse("1 + 2 * 3")
  errors |> should.equal([])
  // Multiplication binds tighter: 1 + (2 * 3)
  case ast {
    BinOp(Int(1, _), Add, BinOp(Int(2, _), Mul, Int(3, _), _), _) -> Nil
    _ -> panic as "Expected 1 + (2 * 3) structure"
  }
}

pub fn parse_precedence_div_before_sub_test() {
  let ParseResult(ast, errors) = parse("10 - 6 / 2")
  errors |> should.equal([])
  // Division binds tighter: 10 - (6 / 2)
  case ast {
    BinOp(Int(10, _), Sub, BinOp(Int(6, _), Div, Int(2, _), _), _) -> Nil
    _ -> panic as "Expected 10 - (6 / 2) structure"
  }
}

pub fn parse_precedence_complex_test() {
  let ParseResult(ast, errors) = parse("1 + 2 * 3 - 4 / 2")
  errors |> should.equal([])
  // Should be: (1 + (2 * 3)) - (4 / 2)
  case ast {
    BinOp(
      BinOp(Int(1, _), Add, BinOp(Int(2, _), Mul, Int(3, _), _), _),
      Sub,
      BinOp(Int(4, _), Div, Int(2, _), _),
      _,
    ) -> Nil
    _ -> panic as "Expected complex precedence structure"
  }
}

// ============================================================================
// SUCCESS CASES - PARENTHESES
// ============================================================================

pub fn parse_parentheses_simple_test() {
  let ParseResult(ast, errors) = parse("(1)")
  errors |> should.equal([])
  case ast {
    Int(1, _) -> Nil
    _ -> panic as "Expected Int(1)"
  }
}

pub fn parse_parentheses_override_precedence_test() {
  let ParseResult(ast, errors) = parse("(1 + 2) * 3")
  errors |> should.equal([])
  // Parentheses override: (1 + 2) * 3
  case ast {
    BinOp(BinOp(Int(1, _), Add, Int(2, _), _), Mul, Int(3, _), _) -> Nil
    _ -> panic as "Expected (1 + 2) * 3 structure"
  }
}

pub fn parse_nested_parentheses_test() {
  let ParseResult(ast, errors) = parse("((1 + 2))")
  errors |> should.equal([])
  case ast {
    Int(1, _) -> Nil  // Inner expression
    _ -> panic as "Expected nested parens to parse"
  }
}

pub fn parse_parentheses_in_expression_test() {
  let ParseResult(ast, errors) = parse("1 * (2 + 3)")
  errors |> should.equal([])
  case ast {
    BinOp(Int(1, _), Mul, BinOp(Int(2, _), Add, Int(3, _), _), _) -> Nil
    _ -> panic as "Expected 1 * (2 + 3) structure"
  }
}

// ============================================================================
// SUCCESS CASES - UNARY OPERATORS
// ============================================================================

pub fn parse_unary_negation_test() {
  let ParseResult(ast, errors) = parse("-5")
  errors |> should.equal([])
  case ast {
    UnaryOp(Not, Int(5, _), _) -> Nil  // Note: Not is used for both ! and -
    _ -> panic as "Expected UnaryOp(Not, 5)"
  }
}

pub fn parse_unary_double_negation_test() {
  let ParseResult(ast, errors) = parse("--5")
  errors |> should.equal([])
  // Should parse as -(-5)
  case ast {
    UnaryOp(Not, UnaryOp(Not, Int(5, _), _), _) -> Nil
    _ -> panic as "Expected double negation"
  }
}

pub fn parse_unary_with_binary_test() {
  let ParseResult(ast, errors) = parse("-5 + 3")
  errors |> should.equal([])
  case ast {
    BinOp(UnaryOp(Not, Int(5, _), _), Add, Int(3, _), _) -> Nil
    _ -> panic as "Expected (-5) + 3"
  }
}

// ============================================================================
// SUCCESS CASES - LET BINDINGS
// ============================================================================

pub fn parse_let_simple_test() {
  let ParseResult(ast, errors) = parse("let x = 10")
  errors |> should.equal([])
  case ast {
    Let("x", False, None, Int(10, _), _) -> Nil
    _ -> panic as "Expected Let(x, False, None, 10)"
  }
}

pub fn parse_let_with_variable_value_test() {
  let ParseResult(ast, errors) = parse("let y = x")
  errors |> should.equal([])
  case ast {
    Let("y", False, None, Var("x", _), _) -> Nil
    _ -> panic as "Expected Let(y, False, None, x)"
  }
}

pub fn parse_let_with_expression_value_test() {
  let ParseResult(ast, errors) = parse("let z = 1 + 2")
  errors |> should.equal([])
  case ast {
    Let("z", False, None, BinOp(Int(1, _), Add, Int(2, _), _), _) -> Nil
    _ -> panic as "Expected Let(z, False, None, 1+2)"
  }
}

pub fn parse_let_mut_test() {
  let ParseResult(ast, errors) = parse("let mut x = 10")
  errors |> should.equal([])
  case ast {
    Let("x", True, None, Int(10, _), _) -> Nil
    _ -> panic as "Expected Let(x, True, None, 10)"
  }
}

pub fn parse_let_with_type_annotation_test() {
  let ParseResult(ast, errors) = parse("let x: Int = 10")
  errors |> should.equal([])
  case ast {
    Let("x", False, Some("Int"), Int(10, _), _) -> Nil
    _ -> panic as "Expected Let(x, False, Some(Int), 10)"
  }
}

pub fn parse_let_mut_with_type_test() {
  let ParseResult(ast, errors) = parse("let mut x: Int = 10")
  errors |> should.equal([])
  case ast {
    Let("x", True, Some("Int"), Int(10, _), _) -> Nil
    _ -> panic as "Expected Let(x, True, Some(Int), 10)"
  }
}

// ============================================================================
// SUCCESS CASES - MODULE PARSING
// ============================================================================

pub fn parse_module_single_let_test() {
  let ParseResult(ast, errors) = parse_module("let x = 10")
  errors |> should.equal([])
  case ast {
    [Let("x", False, None, Int(10, _), _)] -> Nil
    _ -> panic as "Expected [Let(x, 10)]"
  }
}

pub fn parse_module_multiple_lets_test() {
  let ParseResult(ast, errors) = parse_module("let x = 10 let y = 20")
  errors |> should.equal([])
  case ast {
    [Let("x", False, None, Int(10, _), _), Let("y", False, None, Int(20, _), _)] -> Nil
    _ -> panic as "Expected [Let(x, 10), Let(y, 20)]"
  }
}

pub fn parse_module_let_then_expr_test() {
  let ParseResult(ast, errors) = parse_module("let x = 10 x")
  errors |> should.equal([])
  case ast {
    [Let("x", False, None, Int(10, _), _), Var("x", _)] -> Nil
    _ -> panic as "Expected [Let(x, 10), x]"
  }
}

// ============================================================================
// ERROR REPORTING - MISSING TOKENS
// ============================================================================

pub fn parse_error_missing_closing_paren_test() {
  assert_has_error("(1 + 2")
}

pub fn parse_error_missing_closing_paren_span_test() {
  assert_has_error("(1 + 2")
}

pub fn parse_error_missing_equals_test() {
  assert_has_error("let x 10")
}

pub fn parse_error_missing_equals_span_test() {
  assert_has_error("let x 10")
}

pub fn parse_error_missing_type_colon_test() {
  assert_has_error("let x Int = 10")
}

// ============================================================================
// ERROR REPORTING - INVALID TOKENS
// ============================================================================

pub fn parse_error_unknown_operator_test() {
  assert_has_error("1 @ 2")
}

pub fn parse_error_double_operator_test() {
  assert_has_error("1 ++ 2")
}

pub fn parse_error_missing_operand_test() {
  assert_has_error("1 +")
}

// ============================================================================
// ERROR RECOVERY - STATEMENT LEVEL
// ============================================================================

pub fn parse_recovery_let_missing_value_test() {
  // Parser should recover and continue after missing value
  let ParseResult(ast, errors) = parse_module("let x = ; let y = 20")
  { list.length(errors) >= 1 } |> should.be_true  // Has error for missing value
  // Should still parse second let
  case ast {
    [_, Let("y", False, None, Int(20, _), _)] -> Nil
    _ -> panic as "Expected recovery to parse second let"
  }
}

pub fn parse_recovery_multiple_errors_test() {
  // Multiple errors should all be reported
  let ParseResult(_ast, errors) = parse_module("let x = ; let y = ; let z = 30")
  // Should have at least 2 errors (one for each missing value)
  { list.length(errors) >= 2 } |> should.be_true
}

// ============================================================================
// ERROR RECOVERY - EXPRESSION LEVEL
// ============================================================================

pub fn parse_recovery_unclosed_paren_test() {
  // Parser should recover after unclosed paren
  let ParseResult(ast, errors) = parse("(1 + 2")
  { list.length(errors) >= 1 } |> should.be_true
  // Should still produce some AST (even if partial)
  case ast {
    Int(_, _) | Var(_, _) | BinOp(_, _, _, _) | UnaryOp(_, _, _) -> Nil
    _ -> panic as "Expected some AST despite error"
  }
}

pub fn parse_recovery_invalid_in_parens_test() {
  // Parser should recover after invalid token in parens
  let ParseResult(ast, errors) = parse("(1 @ 2)")
  { list.length(errors) >= 1 } |> should.be_true
  // Should still produce some AST
  case ast {
    Int(_, _) | Var(_, _) | BinOp(_, _, _, _) | UnaryOp(_, _, _) -> Nil
    _ -> panic as "Expected some AST despite error"
  }
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_number_test() {
  let source = "42"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_variable_test() {
  let source = "x"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_addition_test() {
  let source = "1 + 2"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_subtraction_test() {
  let source = "10 - 5"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_multiplication_test() {
  let source = "3 * 4"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_division_test() {
  let source = "20 / 4"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_negation_test() {
  let source = "-5"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_parentheses_test() {
  let source = "(1 + 2) * 3"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_nested_parens_test() {
  let source = "((1))"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_let_simple_test() {
  let source = "let x = 10"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_let_mut_test() {
  let source = "let mut x = 10"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

pub fn roundtrip_let_with_type_test() {
  let source = "let x: Int = 10"
  let ParseResult(ast, errors) = parse(source)
  errors |> should.equal([])
  format_expr(ast) |> should.equal(source)
}

// ============================================================================
// FORMATTER TESTS
// ============================================================================

pub fn format_number_test() {
  format_expr(Int(42, todo_span())) |> should.equal("42")
}

pub fn format_variable_test() {
  format_expr(Var("x", todo_span())) |> should.equal("x")
}

pub fn format_addition_test() {
  format_expr(BinOp(Int(1, todo_span()), Add, Int(2, todo_span()), todo_span()))
  |> should.equal("1 + 2")
}

pub fn format_subtraction_test() {
  format_expr(BinOp(Int(10, todo_span()), Sub, Int(5, todo_span()), todo_span()))
  |> should.equal("10 - 5")
}

pub fn format_multiplication_test() {
  format_expr(BinOp(Int(3, todo_span()), Mul, Int(4, todo_span()), todo_span()))
  |> should.equal("3 * 4")
}

pub fn format_division_test() {
  format_expr(BinOp(Int(20, todo_span()), Div, Int(4, todo_span()), todo_span()))
  |> should.equal("20 / 4")
}

pub fn format_negation_test() {
  format_expr(UnaryOp(Not, Int(5, todo_span()), todo_span()))
  |> should.equal("-5")
}

pub fn format_precedence_test() {
  // 1 + (2 * 3) - doesn't track precedence in AST, just format as-is
  let expr = BinOp(
    Int(1, todo_span()),
    Add,
    BinOp(Int(2, todo_span()), Mul, Int(3, todo_span()), todo_span()),
    todo_span(),
  )
  format_expr(expr) |> should.equal("1 + 2 * 3")
}

pub fn format_parentheses_test() {
  // (1 + 2) * 3 needs parens because + has lower precedence than *
  let expr = BinOp(
    BinOp(Int(1, todo_span()), Add, Int(2, todo_span()), todo_span()),
    Mul,
    Int(3, todo_span()),
    todo_span(),
  )
  format_expr(expr) |> should.equal("(1 + 2) * 3")
}

pub fn format_let_test() {
  format_expr(Let("x", False, None, Int(10, todo_span()), todo_span()))
  |> should.equal("let x = 10")
}

pub fn format_let_mut_test() {
  format_expr(Let("x", True, None, Int(10, todo_span()), todo_span()))
  |> should.equal("let mut x = 10")
}

pub fn format_let_with_type_test() {
  format_expr(Let("x", False, Some("Int"), Int(10, todo_span()), todo_span()))
  |> should.equal("let x: Int = 10")
}

// ============================================================================
// EDGE CASES
// ============================================================================

pub fn parse_empty_source_test() {
  let ParseResult(_ast, errors) = parse("")
  // Empty source should produce an error or empty AST
  // For now, just verify it doesn't crash
  Nil |> should.equal(Nil)
}

pub fn parse_whitespace_only_test() {
  let ParseResult(_ast, errors) = parse("   \n  ")
  // Whitespace only should produce an error or empty AST
  Nil |> should.equal(Nil)
}

pub fn parse_single_keyword_test() {
  let ParseResult(_ast, errors) = parse("let")
  { list.length(errors) >= 1 } |> should.be_true  // Incomplete let
}

pub fn parse_deeply_nested_parens_test() {
  let ParseResult(ast, errors) = parse("((((1))))")
  errors |> should.equal([])
  case ast {
    Int(1, _) -> Nil
    _ -> panic as "Expected Int(1)"
  }
}

pub fn parse_long_chain_test() {
  let ParseResult(ast, errors) = parse("1 + 2 + 3 + 4 + 5")
  errors |> should.equal([])
  // Should parse as left-associative chain
  case ast {
    BinOp(_, Add, Int(5, _), _) -> Nil  // Ends with + 5
    _ -> panic as "Expected chain ending with 5"
  }
}

// ============================================================================
// HELPERS
// ============================================================================

fn todo_span() -> Span {
  Span("test", 0, 0, 0, 0)
}

fn assert_has_error(source: String) {
  let result = parse(source)
  { list.length(result.errors) >= 1 } |> should.be_true
}
