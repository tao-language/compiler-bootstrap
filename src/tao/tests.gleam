import core/context.{type Context}
import core/term.{type Term}
import core/value.{type Value}
import syntax/span.{type Span}
import tao/ast.{type Expr, type Module, type Pattern}

pub type TestResult {
  TestResutl(data: TestResultData, name: String, span: Span)
}

pub type TestResultData {
  TestPass
  TestFail(expr: Expr, expect: Pattern, got: Value)
}

pub fn run(
  ctx: Context,
  tests: List(#(String, Term, Expr, Pattern)),
) -> List(TestResult) {
  todo
}
