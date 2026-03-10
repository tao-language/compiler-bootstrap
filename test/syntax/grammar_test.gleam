// ============================================================================
// GRAMMAR DSL TESTS
// ============================================================================
/// Tests for the syntax/grammar module.
/// 
/// The grammar DSL allows defining parsers and formatters from a single
/// grammar definition. Tests verify parsing, operator precedence, and
/// layout handling.
import gleeunit
import gleeunit/should
import examples/calc.{parse, type Expr, Add, Div, Int, Mul, Sub}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn parse_ok(source: String) -> Expr {
  let result = parse(source)
  case result.errors {
    [] -> result.ast
    _ -> panic as "Parse failed"
  }
}

// ============================================================================
// BASIC PARSING TESTS
// ============================================================================

pub fn parse_number_single_digit_test() {
  parse_ok("42") |> should.equal(Int(42))
}

pub fn parse_number_multi_digit_test() {
  parse_ok("123") |> should.equal(Int(123))
}

pub fn parse_number_zero_test() {
  parse_ok("0") |> should.equal(Int(0))
}

// ============================================================================
// ADDITION TESTS
// ============================================================================

pub fn parse_add_simple_test() {
  parse_ok("1 + 2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_add_multiple_test() {
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}

pub fn parse_add_left_associative_test() {
  // 1 + 2 + 3 should parse as (1 + 2) + 3, not 1 + (2 + 3)
  parse_ok("1 + 2 + 3")
  |> should.equal(Add(Add(Int(1), Int(2)), Int(3)))
}

// ============================================================================
// SUBTRACTION TESTS
// ============================================================================

pub fn parse_sub_simple_test() {
  parse_ok("5 - 3") |> should.equal(Sub(Int(5), Int(3)))
}

pub fn parse_sub_left_associative_test() {
  // 10 - 3 - 2 should parse as (10 - 3) - 2
  parse_ok("10 - 3 - 2")
  |> should.equal(Sub(Sub(Int(10), Int(3)), Int(2)))
}

// ============================================================================
// MULTIPLICATION TESTS
// ============================================================================

pub fn parse_mul_simple_test() {
  parse_ok("3 * 4") |> should.equal(Mul(Int(3), Int(4)))
}

pub fn parse_mul_multiple_test() {
  parse_ok("2 * 3 * 4")
  |> should.equal(Mul(Mul(Int(2), Int(3)), Int(4)))
}

// ============================================================================
// DIVISION TESTS
// ============================================================================

pub fn parse_div_simple_test() {
  parse_ok("10 / 2") |> should.equal(Div(Int(10), Int(2)))
}

pub fn parse_div_left_associative_test() {
  // 100 / 10 / 2 should parse as (100 / 10) / 2
  parse_ok("100 / 10 / 2")
  |> should.equal(Div(Div(Int(100), Int(10)), Int(2)))
}

// ============================================================================
// PRECEDENCE TESTS
// ============================================================================

pub fn parse_precedence_mul_before_add_test() {
  // * binds tighter than +, so 1 + 2 * 3 = 1 + (2 * 3)
  parse_ok("1 + 2 * 3")
  |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}

pub fn parse_precedence_mul_before_sub_test() {
  // * binds tighter than -
  parse_ok("5 - 2 * 3")
  |> should.equal(Sub(Int(5), Mul(Int(2), Int(3))))
}

pub fn parse_precedence_div_before_add_test() {
  // / binds tighter than +
  parse_ok("10 + 8 / 2")
  |> should.equal(Add(Int(10), Div(Int(8), Int(2))))
}

pub fn parse_precedence_all_operators_test() {
  // Complex expression with all operators
  parse_ok("1 + 2 * 3 - 4 / 2")
  |> should.equal(Sub(Add(Int(1), Mul(Int(2), Int(3))), Div(Int(4), Int(2))))
}

// ============================================================================
// PARENTHESES TESTS
// ============================================================================

pub fn parse_parens_override_precedence_test() {
  // Parens override precedence: (1 + 2) * 3
  parse_ok("(1 + 2) * 3")
  |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
}

pub fn parse_parens_nested_test() {
  // Nested parentheses
  parse_ok("((1 + 2) * 3)")
  |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
}

pub fn parse_parens_deeply_nested_test() {
  // Deeply nested parentheses
  parse_ok("(((1)))")
  |> should.equal(Int(1))
}

pub fn parse_parens_complex_test() {
  // Complex expression with multiple paren groups
  parse_ok("(1 + 2) * (3 + 4)")
  |> should.equal(Mul(Add(Int(1), Int(2)), Add(Int(3), Int(4))))
}

// ============================================================================
// WHITESPACE TESTS
// ============================================================================

pub fn parse_whitespace_around_operator_test() {
  parse_ok("1+2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_whitespace_multiple_spaces_test() {
  parse_ok("1   +   2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_whitespace_tabs_test() {
  parse_ok("1\t+\t2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_whitespace_newlines_test() {
  parse_ok("1\n+\n2") |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_whitespace_mixed_test() {
  parse_ok("  1  \n  +  \t  2  ") |> should.equal(Add(Int(1), Int(2)))
}
