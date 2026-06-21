import core/context.{type Context}
import core/term.{type Term}
import core/value.{type Value}
import syntax/span.{type Span}
import tao/ast.{type Expr, type Module, type Pattern}

pub type TestDef {
  TestDef(name: String, term: Term, expr: Expr, expect: Pattern)
}

pub type TestResult {
  TestResutl(data: TestResultData, name: String, span: Span)
}

pub type TestResultData {
  TestPass
  TestFail(got: Value, expr: Expr, expect: Pattern)
}

pub fn run(ctx: Context, tests: List(TestDef)) -> List(TestResult) {
  todo
}
