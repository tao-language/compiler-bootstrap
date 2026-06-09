/// End-to-end and integration tests for common examples.
///
/// TODO: parse/format checks
import core/ast
import core/context.{type FFI, Context, new_ctx}
import core/eval.{eval}
import core/infer.{infer}
import core/literals as lit
import core/resolve.{resolve}
import core/term as tm
import core/value.{type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("", 0, 0, 0, 0)

fn int_mul(args: List(Value)) -> Option(Value) {
  case args {
    [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x * y))
    _ -> None
  }
}

fn int_sub(args: List(Value)) -> Option(Value) {
  case args {
    [v.Lit(lit.Int(x)), v.Lit(lit.Int(y))] -> Some(v.int(x - y))
    _ -> None
  }
}

pub fn factorial_test() {
  // TODO: parse/format checks
  // $fix f. $fn(x: ?)
  // => $match(x) {
  // | 0 => 1
  // | n => @int_mul<$Int>(n, f @int_sub(n, 1))
  // }
  let ast_fn =
    ast.fix(
      "f",
      ast.lam(
        #("x", ast.hole(-1, s)),
        ast.match(
          ast.var("x", s),
          [
            ast.Case(ast.pint(0, s), None, ast.int(1, s), s),
            ast.Case(
              ast.pvar("n", s),
              None,
              ast.call(
                "int_mul",
                [
                  ast.var("n", s),
                  ast.app(
                    ast.var("f", s),
                    ast.call(
                      "int_sub",
                      [ast.var("x", s), ast.int(1, s)],
                      ast.int_t(s),
                      s,
                    ),
                    s,
                  ),
                ],
                ast.int_t(s),
                s,
              ),
              s,
            ),
          ],
          s,
        ),
        s,
      ),
      s,
    )

  let ctx0 =
    Context(..new_ctx, ffi: [
      #("int_mul", int_mul),
      #("int_sub", int_sub),
    ])
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
              tm.App(tm.Var(2), tm.Call("int_sub", [tm.Var(1), tm.int(1)])),
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
