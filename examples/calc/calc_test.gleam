// ============================================================================
// CALCULATOR TESTS
// ============================================================================
import examples/calc/ast.{type Expr, Add, Int, Mul}
import examples/calc/syntax.{format, parse}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn parse_number_test() {
  let result = parse("42")
  result.ast |> should.equal(Int(42))
}

pub fn parse_add_test() {
  let result = parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
}

pub fn parse_mul_test() {
  let result = parse("2 * 3")
  result.ast |> should.equal(Mul(Int(2), Int(3)))
}

pub fn parse_precedence_test() {
  // 1 + 2 * 3 should parse as 1 + (2 * 3), not (1 + 2) * 3
  let result = parse("1 + 2 * 3")
  result.ast |> should.equal(Add(Int(1), Mul(Int(2), Int(3))))
}

pub fn parse_parens_test() {
  let result = parse("(1 + 2) * 3")
  result.ast |> should.equal(Mul(Add(Int(1), Int(2)), Int(3)))
}

pub fn format_number_test() {
  format(Int(42)) |> should.equal("42")
}

pub fn format_add_test() {
  format(Add(Int(1), Int(2))) |> should.equal("1 + 2")
}

pub fn format_mul_test() {
  format(Mul(Int(2), Int(3))) |> should.equal("2 * 3")
}

pub fn format_precedence_test() {
  // Should not add unnecessary parens
  format(Add(Int(1), Mul(Int(2), Int(3)))) |> should.equal("1 + 2 * 3")
}

pub fn format_parens_test() {
  // Should preserve necessary parens
  format(Mul(Add(Int(1), Int(2)), Int(3))) |> should.equal("(1 + 2) * 3")
}

pub fn roundtrip_test() {
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
