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

fn op(name: String, call_suffix: String) -> #(String, Value, v.Type) {
  // %for(__type: %Type).
  // %lam(__args: __type) => %match (__type) {
  // | {1: %Int,   2: %Int}   => @int_add<%Int>(__args)
  // | {1: %Float, 2: %Float} => @float_add<%Float>(__args)
  // }
  let for_type = v.For([], #("__type", v.Typ(0)), _)
  let lam_args = tm.Lam(#("__args", tm.Var(0)), _)
  let match_type = tm.Match(tm.Var(1), _)
  let pargs = fn(a) { tm.prcd_strict([#("1", a), #("2", a)]) }
  let call = fn(prefix, ret) { tm.Call(prefix <> call_suffix, ret, tm.Var(0)) }
  let value_cases = [
    tm.Case(pargs(tm.pint_t), None, call("int_", tm.int_t)),
    tm.Case(pargs(tm.pfloat_t), None, call("float_", tm.float_t)),
  ]
  let value = for_type(lam_args(match_type(value_cases)))
  // %for(__type: %Type).
  // %pi(__args: __type) -> %match (__type) {
  // | {1: %Int,   2: %Int}   => %Int
  // | {1: %Float, 2: %Float} => %Float
  // }
  let pi_args = tm.Pi(#("__args", tm.Var(0)), _)
  let type_cases = [
    tm.Case(pargs(tm.pint_t), None, tm.int_t),
    tm.Case(pargs(tm.pfloat_t), None, tm.float_t),
  ]
  let typ = for_type(pi_args(match_type(type_cases)))
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
    |> context.push_var(op("-", "sub"))
    |> context.push_var(op("*", "mul"))
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
