// Regression test for the factorial misquoting bug.
//
// The overloaded operator values (`*`, `-`) beta-reduce to a dispatch match
// `match __type { int => @int_x(args), float => @float_x(args) }` that gets
// stuck on the (neutral) implicit `__type` hole. The stuck `NMatch` captures
// the small beta-reduction env `[record, hole]`, but the record's fields
// carry neutral variables with levels relative to the caller's env. Quoting
// that neutral used to use the captured env for *both* the case body terms'
// de Bruijn indices and the stored values' de Bruijn levels, producing
// negative indices (`2 - 5 - 1 = -4` for `n`, `2 - 2 - 1 = -1` for `f`);
// `list_utils.at` then silently bound them to the head of the env (which is
// `n` in the n-case), turning `f(n-1)` into `n(n-1)` and stalling
// `factorial(n)` at a neutral `int_mul` for every n >= 1.
//
// The fix: `quote_case` evaluates case bodies in the captured *term* frame
// but quotes the result against the placement env (`placeholder_env`), and
// `at` rejects negative indices. These tests pin both halves.
import core/context.{type Context, Context, new_ctx, push_var}
import core/eval.{eval}
import core/ffi
import core/infer.{infer}
import core/resolve
import core/term.{type Term} as tm
import core/value.{type Value} as v
import gleam/list
import gleam/option.{None, Some}
import syntax/span.{Span}
import tao/ast.{type Expr} as tao
import tao/desugar

const s = Span("tao/examples_test", 0, 0, 0, 0)

fn check_expr(ctx: Context, expr: Expr) -> #(Term, Value, Context) {
  let #(term, typ, ctx) = infer(ctx, desugar.expr([], expr))
  let term = resolve.term(ctx.ffi, ctx.subst, ctx.env, term)
  let typ = resolve.value(ctx.ffi, ctx.subst, typ)
  #(term, typ, ctx)
}

fn op(name: String, call_suffix: String) -> #(String, Value, v.Type) {
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
  let pi_args = tm.Pi(#("__args", tm.Var(0)), _)
  let type_cases = [
    tm.Case(pargs(tm.pint_t), None, tm.int_t),
    tm.Case(pargs(tm.pfloat_t), None, tm.float_t),
  ]
  let typ = for_type(pi_args(match_type(type_cases)))
  #(name, value, typ)
}

fn factorial(n: Int) -> Expr {
  // fn f(x) -> Int
  // = match x {
  // | 0 => 1
  // | n => n * factorial(n - 1)
  // }
  let i1 = tao.int(1, s)
  let f = tao.var("f", s)
  let x = tao.var("x", s)
  let n_var = tao.var("n", s)
  let sub = fn(x, y) { tao.app(tao.var("-", s), [#("", x), #("", y)], s) }
  let mul = fn(x, y) { tao.app(tao.var("*", s), [#("", x), #("", y)], s) }
  let case0 = tao.Case(tao.pint(0, s), None, i1)
  let case_ =
    tao.Case(
      tao.pvar("n", s),
      None,
      mul(n_var, tao.app(f, [#("", sub(n_var, i1))], s)),
    )
  let fn_def =
    tao.FnDef(
      name: "f",
      implicits: #([], None),
      params: #([#(tao.pvar("x", s), #(None, None))], None),
      returns: Some(tao.int_t(s)),
      body: tao.match(x, [case0, case_], s),
    )
  tao.do(
    [
      tao.Stmt(fn_def, s),
      tao.return(tao.app(f, [#("", tao.int(n, s))], s), s),
    ],
    s,
  )
}

/// True if the term contains a `tm.Err` or a `Var` with a negative index —
/// the fingerprints of the misquoting bug.
fn has_err_or_negative_var(t: Term) -> Bool {
  case t {
    tm.Err -> True
    tm.Var(i) -> i < 0
    tm.Var(_) -> False
    tm.Typ(_) -> False
    tm.Hole(_) -> False
    tm.Lit(_) -> False
    tm.LitT(_) -> False
    tm.Ctr(_, a) -> has_err_or_negative_var(a)
    tm.Rcd(fields, tail) -> {
      let fields_bad =
        list.any(fields, fn(field) {
          let #(_, #(f, d)) = field
          has_err_or_negative_var(f)
            || case d {
              Some(d) -> has_err_or_negative_var(d)
              None -> False
            }
        })
      let tail_bad = case tail {
        Some(t) -> has_err_or_negative_var(t)
        None -> False
      }
      fields_bad || tail_bad
    }
    tm.Call(_, r, a) -> has_err_or_negative_var(r) || has_err_or_negative_var(a)
    tm.Ann(t, r) -> has_err_or_negative_var(t) || has_err_or_negative_var(r)
    tm.For(_, b) -> has_err_or_negative_var(b)
    tm.Lam(_, b) -> has_err_or_negative_var(b)
    tm.Pi(_, b) -> has_err_or_negative_var(b)
    tm.Fix(_, b) -> has_err_or_negative_var(b)
    tm.App(f, a) -> has_err_or_negative_var(f) || has_err_or_negative_var(a)
    tm.Match(a, cases) -> {
      let cases_bad =
        list.any(cases, fn(c) {
          let tm.Case(_, g, b) = c
          let guard_bad = case g {
            Some(#(gt, _)) -> has_err_or_negative_var(gt)
            None -> False
          }
          guard_bad || has_err_or_negative_var(b)
        })
      has_err_or_negative_var(a) || cases_bad
    }
    tm.TypeDef(_) -> False
  }
}

pub fn factorial_overload_recursion_regression_test() {
  let ctx0 =
    Context(..new_ctx, ffi: ffi.build)
    |> push_var(op("-", "sub"))
    |> push_var(op("*", "mul"))

  // n = 1 is the smallest case that enters the recursive (n) branch, where
  // the dispatch match on the `__type` holes gets stuck and must be quoted.
  let #(term, type_, ctx) = check_expr(ctx0, factorial(1))
  assert ctx.errors == []
  assert type_ == v.int_t
  // The resolved term must be clean: no Errs, no negative de Bruijn indices.
  assert !has_err_or_negative_var(term)
  assert eval(ctx.ffi, ctx.env, term) == v.int(1)
}

pub fn factorial_overload_recursion_values_test() {
  let ctx0 =
    Context(..new_ctx, ffi: ffi.build)
    |> push_var(op("-", "sub"))
    |> push_var(op("*", "mul"))

  let expected = [1, 1, 2, 6, 24, 120]
  let _ =
    list.index_map(expected, fn(expected, i) {
      let n = i
      let #(term, _, ctx) = check_expr(ctx0, factorial(n))
      assert ctx.errors == []
      assert !has_err_or_negative_var(term)
      assert eval(ctx.ffi, ctx.env, term) == v.int(expected)
      i
    })
  True
}
