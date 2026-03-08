// ============================================================================
// CALCULATOR TESTS
// ============================================================================
/// End-to-end tests for the calculator language

import calc/ast.{Add, Int, Mul}
import calc/eval
import calc/syntax
import gleeunit
import gleeunit/should

pub fn main() -> Nil {
  gleeunit.main()
}

// ============================================================================
// PARSING TESTS
// ============================================================================

pub fn parse_int_test() {
  let result = syntax.parse("42")
  
  result.ast |> should.equal(Int(42))
}

pub fn parse_add_test() {
  let result = syntax.parse("1 + 2")
  
  result.ast |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_mul_test() {
  let result = syntax.parse("2 * 3")
  
  result.ast |> should.equal(Mul(Int(2), Int(3)))
}

pub fn parse_parens_test() {
  let result = syntax.parse("(1 + 2)")
  
  result.ast |> should.equal(Add(Int(1), Int(2)))
}

// ============================================================================
// PRECEDENCE TESTS
// ============================================================================

pub fn precedence_mul_before_add_test() {
  // 2 + 3 * 4 should parse as 2 + (3 * 4)
  let result = syntax.parse("2 + 3 * 4")
  
  let expected = Add(Int(2), Mul(Int(3), Int(4)))
  result.ast |> should.equal(expected)
}

pub fn precedence_parens_override_test() {
  // (2 + 3) * 4 should parse as (2 + 3) * 4
  let result = syntax.parse("(2 + 3) * 4")
  
  let expected = Mul(Add(Int(2), Int(3)), Int(4))
  result.ast |> should.equal(expected)
}

pub fn precedence_left_associative_add_test() {
  // 1 + 2 + 3 should parse as (1 + 2) + 3
  let result = syntax.parse("1 + 2 + 3")
  
  let expected = Add(Add(Int(1), Int(2)), Int(3))
  result.ast |> should.equal(expected)
}

pub fn precedence_left_associative_mul_test() {
  // 2 * 3 * 4 should parse as (2 * 3) * 4
  let result = syntax.parse("2 * 3 * 4")
  
  let expected = Mul(Mul(Int(2), Int(3)), Int(4))
  result.ast |> should.equal(expected)
}

// ============================================================================
// EVALUATION TESTS
// ============================================================================

pub fn eval_int_test() {
  eval.eval(Int(42)) |> should.equal(42)
}

pub fn eval_add_test() {
  let expr = Add(Int(1), Int(2))
  eval.eval(expr) |> should.equal(3)
}

pub fn eval_mul_test() {
  let expr = Mul(Int(2), Int(3))
  eval.eval(expr) |> should.equal(6)
}

pub fn eval_precedence_test() {
  // 2 + 3 * 4 = 2 + 12 = 14
  let result = syntax.parse("2 + 3 * 4")
  
  eval.eval(result.ast) |> should.equal(14)
}

pub fn eval_parens_test() {
  // (2 + 3) * 4 = 5 * 4 = 20
  let result = syntax.parse("(2 + 3) * 4")
  
  eval.eval(result.ast) |> should.equal(20)
}

pub fn eval_left_assoc_test() {
  // 1 + 2 + 3 = 6
  let result = syntax.parse("1 + 2 + 3")
  
  eval.eval(result.ast) |> should.equal(6)
}

// ============================================================================
// FORMATTING TESTS
// ============================================================================

pub fn format_int_test() {
  syntax.format(Int(42)) |> should.equal("42")
}

pub fn format_add_test() {
  let expr = Add(Int(1), Int(2))
  syntax.format(expr) |> should.equal("1 + 2")
}

pub fn format_mul_test() {
  let expr = Mul(Int(2), Int(3))
  syntax.format(expr) |> should.equal("2 * 3")
}

pub fn format_precedence_test() {
  // Should not add unnecessary parens
  let result = syntax.parse("2 + 3 * 4")
  
  syntax.format(result.ast) |> should.equal("2 + 3 * 4")
}

pub fn format_parens_test() {
  // Should preserve necessary parens
  let result = syntax.parse("(2 + 3) * 4")
  
  syntax.format(result.ast) |> should.equal("(2 + 3) * 4")
}

// ============================================================================
// ROUND-TRIP TESTS
// ============================================================================

pub fn roundtrip_int_test() {
  let source = "42"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

pub fn roundtrip_add_test() {
  let source = "1 + 2"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

pub fn roundtrip_mul_test() {
  let source = "2 * 3"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

pub fn roundtrip_precedence_test() {
  let source = "2 + 3 * 4"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

pub fn roundtrip_parens_test() {
  let source = "(2 + 3) * 4"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

pub fn roundtrip_nested_test() {
  let source = "((1 + 2) * 3 + 4) * 5"
  
  let result = syntax.parse(source)
  let formatted = syntax.format(result.ast)
  
  formatted |> should.equal(source)
}

// ============================================================================
// END-TO-END TESTS
// ============================================================================

pub fn e2e_simple_add_test() {
  let source = "1 + 2"
  
  let result = syntax.parse(source)
  let value = eval.eval(result.ast)
  let formatted = syntax.format(result.ast)
  
  value |> should.equal(3)
  formatted |> should.equal(source)
}

pub fn e2e_precedence_test() {
  let source = "2 + 3 * 4"
  
  let result = syntax.parse(source)
  let value = eval.eval(result.ast)
  let formatted = syntax.format(result.ast)
  
  value |> should.equal(14)
  formatted |> should.equal(source)
}

pub fn e2e_parens_test() {
  let source = "(2 + 3) * 4"
  
  let result = syntax.parse(source)
  let value = eval.eval(result.ast)
  let formatted = syntax.format(result.ast)
  
  value |> should.equal(20)
  formatted |> should.equal(source)
}

pub fn e2e_complex_test() {
  let source = "((1 + 2) * 3 + 4) * 5"
  
  let result = syntax.parse(source)
  let value = eval.eval(result.ast)
  let formatted = syntax.format(result.ast)
  
  // ((1 + 2) * 3 + 4) * 5 = (3 * 3 + 4) * 5 = (9 + 4) * 5 = 13 * 5 = 65
  value |> should.equal(65)
  formatted |> should.equal(source)
}
