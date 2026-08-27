import core/context.{type Context}
import core/error.{type Error}
import core/eval.{eval}
import core/term.{type Term}
import core/unwrap.{unwrap}
import core/value.{type Value} as v
import tao/ast.{type Expr, type Pattern}

pub type TestDef {
  TestDef(name: String, term: Term, expr: Expr, expect: Pattern)
}

pub type TestResult {
  TestPass(name: String)
  TestFail(name: String, got: Value, expr: Expr, expect: Pattern)
  TestNeutral(name: String, got: Value, expr: Expr, expect: Pattern)
}

pub type TestResultSummary {
  TestResultSummary(
    errors: List(Error),
    results: List(TestResult),
    num_pass: Int,
    num_fail: Int,
    num_neutral: Int,
  )
}

pub fn run_all(ctx: Context, tests: List(TestDef)) -> TestResultSummary {
  case tests {
    [] -> TestResultSummary(ctx.errors, [], 0, 0, 0)
    [t, ..tests] -> {
      let res = run(ctx, t)
      let summary = run_all(ctx, tests)
      let summary =
        TestResultSummary(..summary, results: [res, ..summary.results])
      case res {
        TestPass(..) ->
          TestResultSummary(..summary, num_pass: summary.num_pass + 1)
        TestFail(..) ->
          TestResultSummary(..summary, num_fail: summary.num_fail + 1)
        TestNeutral(..) ->
          TestResultSummary(..summary, num_neutral: summary.num_neutral + 1)
      }
    }
  }
}

pub fn run(ctx: Context, t: TestDef) -> TestResult {
  // Eval the test's value, then unwrap it: the test body is typically a
  // neutral match over an FFI call (e.g. `@int_add({3, 2})`), and unwrap
  // drives the FFI call to a concrete value so the match can reduce.
  let value = t.term
    |> eval(ctx.ffi, ctx.env, _)
    |> unwrap(ctx.ffi, ctx.subst, _)
  case value {
    v.Ctr("Pass", _) -> TestPass(t.name)
    v.Ctr("Fail", got) -> TestFail(t.name, got, t.expr, t.expect)
    got -> TestNeutral(t.name, got, t.expr, t.expect)
  }
}
