import calc/ast.{Add, Int}
import calc/grammar
import gleeunit
import gleeunit/should

pub fn main() -> Nil {
  gleeunit.main()
}

pub fn debug_parse_test() {
  let result = grammar.parse("1 + 2")
  result.ast |> should.equal(Add(Int(1), Int(2)))
}
