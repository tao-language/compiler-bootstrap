import core/context.{type Context, Context, new_ctx}
import core/eval.{eval}
import core/ffi
import core/infer.{infer}
import core/term.{type Term} as tm
import core/value.{type Value} as v
import gleam/int
import gleam/io
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast.{type Expr} as tao
import tao/desugar

const s = Span("tao/examples_test", 0, 0, 0, 0)

pub fn check_expr(ctx: Context, expr: Expr) -> #(Term, Value, Context) {
  infer(ctx, desugar.expr([], expr))
}

fn op(
  name: String,
  call: String,
  args: List(v.Type),
  ret: tm.Type,
) -> #(String, Value, v.Type) {
  let args_fields =
    list.index_map(args, fn(arg, i) { #(int.to_string(i + 1), arg) })
  let args_rcd = #("args", v.rcd(args_fields))
  let value = v.Lam([], args_rcd, tm.Call(call, ret, tm.Var(0)))
  let typ = v.Pi([], args_rcd, ret)
  #(name, value, typ)
}

pub fn tao_factorial_test() {
  // fn f(x) -> Int
  // = match x {
  // | 0 => 1
  // | n => n * factorial(n - 1)
  // }
  let i1 = tao.int(1, s)
  let #(f, x, n) = #(tao.var("f", s), tao.var("x", s), tao.var("n", s))
  let sub = fn(x, y) { tao.app(tao.var("-", s), [#("", x), #("", y)], s) }
  let mul = fn(x, y) { tao.app(tao.var("*", s), [#("", x), #("", y)], s) }
  let case0 = tao.Case(tao.pint(0, s), None, i1)
  let case_ =
    tao.Case(tao.pvar("n", s), None, mul(n, tao.app(f, [#("", sub(n, i1))], s)))
  let fn_def =
    tao.FnDef(
      name: "f",
      implicits: #([], None),
      params: #([#(tao.pvar("x", s), #(None, None))], None),
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
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> context.push_var(op("-", "int_sub", [v.int_t, v.int_t], tm.int_t))
    |> context.push_var(op("*", "int_mul", [v.int_t, v.int_t], tm.int_t))
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
