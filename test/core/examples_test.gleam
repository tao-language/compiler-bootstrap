/// End-to-end and integration tests for common examples.
///
/// TODO: parse/format checks
import core/ast
import core/context.{Context, new_ctx}
import core/eval.{eval}
import core/ffi
import core/infer.{infer}
import core/resolve.{resolve}
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None}
import syntax/span.{Span}

const s = Span("", 0, 0, 0, 0)

pub fn factorial_test() {
  // TODO: parse/format checks
  // $fix f. $fn(x: ?)
  // => $match(x) {
  // | 0 => 1
  // | n => @int_mul<$Int>(n, f @int_sub(n, 1))
  // }
  let #(f, x, n) = #(ast.var("f", s), ast.var("x", s), ast.var("n", s))
  let i1 = ast.int(1, s)
  let mul = fn(x, y) { ast.call("int_mul", [x, y], ast.int_t(s), s) }
  let sub = fn(x, y) { ast.call("int_sub", [x, y], ast.int_t(s), s) }
  let case0 = ast.Case(ast.pint(0, s), None, ast.int(1, s), s)
  let case_n =
    ast.Case(ast.pvar("n", s), None, mul(n, ast.app(f, sub(n, i1), s)), s)
  let ast_fn =
    ast.fix(
      "f",
      ast.lam(#("x", ast.hole(-1, s)), ast.match(x, [case0, case_n], s), s),
      s,
    )

  let ctx0 = Context(..new_ctx, ffi: ffi.build)
  let #(term, type_, ctx) = infer(ctx0, ast_fn)
  assert ctx.errors == []
  let term = resolve(ctx.ffi, ctx.subst, list.length(ctx.env), term)
  assert term
    == tm.Fix(
      "f",
      tm.Lam(
        #("x", tm.int_t),
        tm.Match(tm.Var(0), [
          tm.Case(tm.pint(0), None, tm.int(1)),
          tm.Case(
            tm.pvar("n"),
            None,
            tm.Call("int_mul", [
              tm.Var(0),
              tm.App(tm.Var(2), tm.Call("int_sub", [tm.Var(0), tm.int(1)])),
            ]),
          ),
        ]),
      ),
    )
  assert type_
    == v.Pi(
      [v.var(0)],
      False,
      #("x", v.int_t),
      tm.Match(tm.Var(0), [
        tm.Case(tm.pint(0), None, tm.int_t),
        tm.Case(tm.pvar("n"), None, tm.int_t),
      ]),
    )
  let factorial = fn(n) { eval(ctx.ffi, ctx.env, tm.App(term, tm.int(n))) }
  assert factorial(0) == v.int(1)
  assert factorial(1) == v.int(1)
  assert factorial(2) == v.int(2)
  assert factorial(3) == v.int(6)
  assert factorial(4) == v.int(24)
  assert factorial(5) == v.int(120)
}
