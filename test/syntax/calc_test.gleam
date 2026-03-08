// ============================================================================
// CALCULATOR TESTS
// ============================================================================
import examples/calc.{Int, format, parse}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

pub fn parse_number_test() {
  let result = parse("42")
  result.ast |> should.equal(Int(42))
  result.errors |> should.equal([])
}

pub fn format_number_test() {
  format(Int(42)) |> should.equal("<ast>")
}
