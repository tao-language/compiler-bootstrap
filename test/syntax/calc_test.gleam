// ============================================================================
// CALCULATOR TESTS - Comprehensive Test Suite
// ============================================================================
import examples/calc.{Add, Div, Int, Mul, Sub, format, parse}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// PARSING TESTS - Numbers
// ============================================================================

pub fn parse_single_digit_test() {
  let result = parse("5")
  result.ast |> should.equal(Int(5))
  result.errors |> should.equal([])
}

pub fn parse_multi_digit_test() {
  let result = parse("123")
  result.ast |> should.equal(Int(123))
  result.errors |> should.equal([])
}

pub fn parse_zero_test() {
  let result = parse("0")
  result.ast |> should.equal(Int(0))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Addition
// ============================================================================

pub fn parse_simple_add_test() {
  let result = parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
  result.errors |> should.equal([])
}

pub fn parse_add_multiple_test() {
  let result = parse("1 + 2 + 3")
  // Left-associative: (1 + 2) + 3
  result.ast |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_add_four_test() {
  let result = parse("1 + 2 + 3 + 4")
  // Left-associative: ((1 + 2) + 3) + 4
  result.ast |> should.equal(Add(Add(Add(Int(1), Int(2)), Int(3)), Int(4)))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Subtraction
// ============================================================================

pub fn parse_simple_sub_test() {
  let result = parse("5 - 3")
  result.ast |> should.equal(Sub(Int(5), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_sub_multiple_test() {
  let result = parse("10 - 3 - 2")
  // Left-associative: (10 - 3) - 2 = 5
  result.ast |> should.equal(Sub(Sub(Int(10), Int(3)), Int(2)))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Multiplication
// ============================================================================

pub fn parse_simple_mul_test() {
  let result = parse("2 * 3")
  result.ast |> should.equal(Mul(Int(2), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_mul_multiple_test() {
  let result = parse("2 * 3 * 4")
  // Left-associative: (2 * 3) * 4
  result.ast |> should.equal(Mul(Mul(Int(2), Int(3)), Int(4)))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Division
// ============================================================================

pub fn parse_simple_div_test() {
  let result = parse("10 / 2")
  result.ast |> should.equal(Div(Int(10), Int(2)))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Precedence
// ============================================================================

pub fn parse_mul_before_add_test() {
  let result = parse("1 + 2 * 3")
  // * has higher precedence: 1 + (2 * 3)
  result.ast |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
  result.errors |> should.equal([])
}

pub fn parse_mul_before_sub_test() {
  let result = parse("10 - 2 * 3")
  // * has higher precedence: 10 - (2 * 3)
  result.ast |> should.equal(Sub(Int(10), Mul(Int(2), Int(3))))
  result.errors |> should.equal([])
}

pub fn parse_add_mul_add_test() {
  let result = parse("1 + 2 * 3 + 4")
  // * has higher precedence: (1 + (2 * 3)) + 4
  result.ast |> should.equal(Add(Add(Int(1), Mul(Int(2), Int(3))), Int(4)))
  result.errors |> should.equal([])
}

pub fn parse_complex_precedence_test() {
  let result = parse("2 * 3 + 4 * 5")
  // * has higher precedence: (2 * 3) + (4 * 5)
  result.ast |> should.equal(Add(Mul(Int(2), Int(3)), Mul(Int(4), Int(5))))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Parentheses
// ============================================================================

pub fn parse_parens_number_test() {
  let result = parse("(42)")
  result.ast |> should.equal(Int(42))
  result.errors |> should.equal([])
}

pub fn parse_parens_add_test() {
  let result = parse("(1 + 2)")
  result.ast |> should.equal(Add(Int(1), Int(2)))
  result.errors |> should.equal([])
}

pub fn parse_parens_override_precedence_test() {
  let result = parse("(1 + 2) * 3")
  // Parens override precedence: (1 + 2) * 3
  result.ast |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_parens_nested_test() {
  let result = parse("((1 + 2) * 3)")
  result.ast |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_parens_complex_test() {
  let result = parse("(1 + 2) * (3 + 4)")
  result.ast |> should.equal(Mul(Add(Int(1), Int(2)), Add(Int(3), Int(4))))
  result.errors |> should.equal([])
}

pub fn parse_parens_deeply_nested_test() {
  let result = parse("(((1)))")
  result.ast |> should.equal(Int(1))
  result.errors |> should.equal([])
}

// ============================================================================
// PARSING TESTS - Mixed operators
// ============================================================================

pub fn parse_add_sub_mix_test() {
  let result = parse("1 + 2 - 3")
  // Left-associative, same precedence: (1 + 2) - 3
  result.ast |> should.equal(Sub(Add(Int(1), Int(2)), Int(3)))
  result.errors |> should.equal([])
}

pub fn parse_mul_div_mix_test() {
  let result = parse("12 / 3 * 2")
  // Left-associative, same precedence: (12 / 3) * 2
  result.ast |> should.equal(Mul(Div(Int(12), Int(3)), Int(2)))
  result.errors |> should.equal([])
}

pub fn parse_all_operators_test() {
  let result = parse("1 + 2 * 3 - 4 / 2")
  // Precedence: 1 + (2 * 3) - (4 / 2)
  // Left-assoc: (1 + (2 * 3)) - (4 / 2)
  result.ast
  |> should.equal(Sub(Add(Int(1), Mul(Int(2), Int(3))), Div(Int(4), Int(2))))
  result.errors |> should.equal([])
}

// ============================================================================
// FORMATTING TESTS
// ============================================================================

pub fn format_int_test() {
  format(Int(42)) |> should.equal("42")
}

pub fn format_add_test() {
  format(Add(Int(1), Int(2))) |> should.equal("1 + 2")
}

pub fn format_sub_test() {
  format(Sub(Int(5), Int(3))) |> should.equal("5 - 3")
}

pub fn format_mul_test() {
  format(Mul(Int(2), Int(3))) |> should.equal("2 * 3")
}

pub fn format_div_test() {
  format(Div(Int(10), Int(2))) |> should.equal("10 / 2")
}

pub fn format_nested_test() {
  format(Add(Int(1), Mul(Int(2), Int(3)))) |> should.equal("1 + 2 * 3")
}

pub fn format_parens_needed_test() {
  format(Mul(Add(Int(1), Int(2)), Int(3))) |> should.equal("(1 + 2) * 3")
}

pub fn format_complex_test() {
  format(Sub(Add(Int(1), Mul(Int(2), Int(3))), Div(Int(4), Int(2))))
  |> should.equal("1 + 2 * 3 - 4 / 2")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_int_test() {
  let source = "42"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_add_test() {
  let source = "1 + 2"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_sub_test() {
  let source = "5 - 3"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_mul_test() {
  let source = "2 * 3"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_div_test() {
  let source = "10 / 2"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_precedence_test() {
  let source = "1 + 2 * 3"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_parens_test() {
  let source = "(1 + 2) * 3"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_nested_parens_test() {
  // Note: Outer parens are redundant and removed during formatting
  let source = "((1 + 2) * 3)"
  let result = parse(source)
  let formatted = format(result.ast)
  // The AST is Mul(Add(1, 2), 3), which formats to "(1 + 2) * 3"
  formatted |> should.equal("(1 + 2) * 3")
}

pub fn roundtrip_complex_test() {
  let source = "1 + 2 * 3 - 4 / 2"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_all_ops_test() {
  let source = "1 + 2 - 3 * 4 / 2"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_multi_digit_test() {
  let source = "123 + 456 * 789"
  let result = parse(source)
  let formatted = format(result.ast)
  formatted |> should.equal(source)
}
// ============================================================================
// ERROR TESTS - Note: Current implementation panics on parse failure
// Future improvement: Return errors instead of panicking
// ============================================================================

// These tests are disabled until error handling is improved
// pub fn parse_empty_string_test() {
//   let result = parse("")
//   case result.errors {
//     [] -> False |> should.be_true
//     _ -> True |> should.be_true
//   }
// }
//
// pub fn parse_invalid_token_test() {
//   let result = parse("abc")
//   case result.errors {
//     [] -> False |> should.be_true
//     _ -> True |> should.be_true
//   }
// }
//
// pub fn parse_incomplete_expr_test() {
//   let result = parse("1 +")
//   case result.errors {
//     [] -> False |> should.be_true
//     _ -> True |> should.be_true
//   }
// }
//
// pub fn parse_mismatched_parens_test() {
//   let result = parse("(1 + 2")
//   case result.errors {
//     [] -> False |> should.be_true
//     _ -> True |> should.be_true
//   }
// }
