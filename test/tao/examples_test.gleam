import core/context.{type Context, Context, new_ctx}
import core/eval.{eval}
import core/ffi
import core/infer.{infer}
import core/term.{type Term}
import core/value.{type Value} as v
import gleam/io
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast.{type Expr} as tao
import tao/desugar

const s = Span("tao/examples_test", 0, 0, 0, 0)

pub fn check_expr(ctx: Context, expr: Expr) -> #(Term, Value, Context) {
  infer(ctx, desugar.expr(expr))
}

pub fn tao_factorial_test() {
  // fn f(x) -> Int
  // = match x {
  // | 0 => 1
  // | n => @int_mul<Int>(n, f(@int_sub<Int>(n, 1)))
  // }
  let i1 = tao.int(1, s)
  let #(f, x, n) = #(tao.var("f", s), tao.var("x", s), tao.var("n", s))
  let sub = fn(x, y) { tao.call("int_sub", tao.int_t(s), [x, y], s) }
  let mul = fn(x, y) { tao.call("int_mul", tao.int_t(s), [x, y], s) }
  let case0 = tao.Case(tao.pint(0, s), None, i1)
  let case_ =
    tao.Case(tao.pvar("n", s), None, mul(n, tao.app(f, [#("", sub(n, i1))], s)))
  let fn_def =
    tao.FnDef(
      name: "f",
      implicits: [],
      implicits_tail: None,
      params: [#(tao.pvar("x", s), #(None, None))],
      params_tail: None,
      returns: Some(tao.int_t(s)),
      body: tao.match(x, [case0, case_], s),
    )
  let factorial = fn(n) {
    tao.do(
      [
        tao.Stmt(fn_def, s),
        tao.return(tao.app(f, [#("", tao.int(n, s))], s), s),
      ],
      s,
    )
  }
  io.println("\n")
  let ctx = Context(..new_ctx, ffi: ffi.build)
  // factorial(0) = 1
  let #(term, type_, ctx) = check_expr(ctx, factorial(0))
  assert ctx.errors == []
  assert type_ == v.int_t
  assert eval(ctx.ffi, ctx.env, term) == v.int(1)
  // factorial(1) = 1
  let #(term, type_, ctx) = check_expr(ctx, factorial(1))
  assert ctx.errors == []
  assert type_ == v.int_t
  assert eval(ctx.ffi, ctx.env, term) == v.int(1)
  // factorial(2) = 2
  let #(term, _, ctx) = check_expr(ctx, factorial(2))
  assert eval(ctx.ffi, ctx.env, term) == v.int(2)
  // factorial(3) = 6
  let #(term, _, ctx) = check_expr(ctx, factorial(3))
  assert eval(ctx.ffi, ctx.env, term) == v.int(6)
  // factorial(4) = 24
  let #(term, _, ctx) = check_expr(ctx, factorial(4))
  assert eval(ctx.ffi, ctx.env, term) == v.int(24)
  // factorial(5) = 120
  let #(term, _, ctx) = check_expr(ctx, factorial(5))
  assert eval(ctx.ffi, ctx.env, term) == v.int(120)
}
