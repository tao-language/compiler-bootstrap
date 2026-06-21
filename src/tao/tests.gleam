import core/context.{type Context}
import core/eval.{eval}
import core/term.{type Term}
import core/value.{type Value} as v
import gleam/list
import tao/ast.{type Expr, type Pattern}

pub type TestDef {
  TestDef(name: String, term: Term, expr: Expr, expect: Pattern)
}

pub type TestResult {
  TestPass(name: String)
  TestFail(name: String, got: Value, expr: Expr, expect: Pattern)
  TestNeutral(name: String, got: Value, expr: Expr, expect: Pattern)
}

pub fn run(ctx: Context, tests: List(TestDef)) -> List(TestResult) {
  list.map(tests, fn(t) {
    case eval(ctx.ffi, ctx.env, t.term) {
      v.Ctr("Pass", _) -> TestPass(t.name)
      v.Ctr("Fail", got) -> TestFail(t.name, got, t.expr, t.expect)
      got -> TestNeutral(t.name, got, t.expr, t.expect)
    }
  })
}
