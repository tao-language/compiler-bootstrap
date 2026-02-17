import core as c
import gleam/option.{None, Some}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// --- Typ --- \\
pub fn typ_eval_test() {
  c.eval([], typ(0)) |> should.equal(c.VTyp(0))
  c.eval([], typ(1)) |> should.equal(c.VTyp(1))
}

pub fn typ_infer_test() {
  c.infer(42, [], typ(0)) |> should.equal(c.VTyp(1))
}

pub fn typ_check_test() {
  c.check(42, [], typ(0), c.VTyp(1)) |> should.equal(c.VTyp(1))
  c.check(42, [], typ(0), c.VTyp(2))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(1), s(), None)))
}

// --- Lit --- \\
pub fn lit_eval_test() {
  c.eval([], lit(c.I32(42))) |> should.equal(c.VLit(c.I32(42)))
}

// --- LitT --- \\
pub fn lit_t_eval_test() {
  c.eval([], lit_t(c.I32T)) |> should.equal(c.VLitT(c.I32T))
}

// --- Var --- \\
pub fn var_eval_test() {
  // c.eval([], var(0)) |> should.equal(VNeut(HVar(0), []))
  c.eval([], var(0)) |> should.equal(c.VErr(c.UnboundVar(0, s())))
  c.eval([c.VTyp(1)], var(0)) |> should.equal(c.VTyp(1))
}

pub fn var_infer_test() {
  let ctx = [#("x", c.VTyp(0))]
  c.infer(42, ctx, var(0)) |> should.equal(c.VTyp(0))
  c.infer(42, ctx, var(1))
  |> should.equal(c.VErr(c.UnboundVar(1, s())))
}

// --- Ctr --- \\
pub fn ctr_eval_test() {
  let env = [c.VTyp(42)]
  c.eval(env, ctr("A", [var(0)])) |> should.equal(c.VCtr("A", [c.VTyp(42)]))
}

// --- Ann --- \\
pub fn ann_eval_test() {
  let env = [c.VTyp(42)]
  c.eval(env, ann(var(0), typ(1))) |> should.equal(c.VTyp(42))
}

// --- Lam --- \\
// pub fn lam_eval_test() {
//   // Since we can't compare the closure directly, resolve it first.
//   // Capture it into a VCtr to get the name and output.
//   let eval_lam = fn(env, name, output) {
//     case c.eval(env, lam(name, output)) {
//       VLam(x, output) -> VCtr(x, [output(VTyp(42))])
//       value -> value
//     }
//   }
//   eval_lam([], "a", typ(1)) |> should.equal(VCtr("a", [VTyp(1)]))
//   eval_lam([], "b", var(0)) |> should.equal(VCtr("b", [VTyp(42)]))
//   eval_lam([], "c", var(1))
//   |> should.equal(VCtr("c", [VErr(c.UnboundVar(1, s()))]))
// }

// --- Pi --- \\
// pub fn pi_eval_test() {
//   // Since we can't compare the closure directly, resolve it first.
//   // Capture it into a VCtr to get the name, input, and output.
//   let eval_pi = fn(env, name, in, out) {
//     case c.eval(env, pi(name, in, out)) {
//       c.VPi(x, env, input, output) -> c.VCtr(x, [input, output(VTyp(42))])
//       value -> value
//     }
//   }
//   eval_pi([], "a", typ(1), typ(2))
//   |> should.equal(VCtr("a", [VTyp(1), VTyp(2)]))
//   eval_pi([], "b", typ(1), var(0))
//   |> should.equal(VCtr("b", [VTyp(1), VTyp(42)]))
//   eval_pi([], "c", typ(1), var(1))
//   |> should.equal(VCtr("c", [VTyp(1), VErr(c.UnboundVar(1, s()))]))
// }

// --- App --- \\
pub fn app_eval_test() {
  let env = [c.VLam("a", [], var(0))]
  c.eval(env, app(typ(0), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VTyp(0), s())))
  c.eval(env, app(var(0), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(var(1), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VErr(c.UnboundVar(1, s())), s())))
  case c.eval(env, app(pi("a", typ(0), typ(1)), typ(42))) {
    c.VErr(c.NotAFunction(_, _)) -> True
    _ -> False
  }
  |> should.equal(True)
  c.eval(env, app(lam("a", var(0)), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(ann(var(0), typ(1)), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(ctr("A", [typ(1)]), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VCtr("A", [c.VTyp(1)]), s())))
}

// --- Match --- \\
pub fn match_eval_test() {
  let i1 = lit(c.I32(1))
  let i2 = lit(c.I32(2))
  match(ctr("Just", [i1]), [
    c.Case(c.PCtr("Nothing", []), i2, s()),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s()),
  ])
  |> c.eval([], _)
  |> should.equal(c.VLit(c.I32(1)))

  match(ctr("Nothing", []), [
    c.Case(c.PCtr("Nothing", []), i2, s()),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s()),
  ])
  |> c.eval([], _)
  |> should.equal(c.VLit(c.I32(2)))

  match(ctr("Null", []), [
    c.Case(c.PCtr("Nothing", []), i2, s()),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s()),
  ])
  |> c.eval([], _)
  |> should.equal(c.VErr(c.MatchUnhandledCase(c.VCtr("Null", []), s())))
}

// --- Err --- \\
// TODO

// --- HELPERS to make writing ASTs less painful ---
fn s() {
  c.Span("core_test", 1, 1)
}

fn typ(l) {
  c.Term(c.Typ(l), s())
}

fn lit(v) {
  c.Term(c.Lit(v), s())
}

fn lit_t(t) {
  c.Term(c.LitT(t), s())
}

fn var(i) {
  c.Term(c.Var(i), s())
}

fn ctr(k, args) {
  c.Term(c.Ctr(k, args), s())
}

fn pi(name, in, out) {
  c.Term(c.Pi(name, in, out), s())
}

fn lam(name, body) {
  c.Term(c.Lam(name, body), s())
}

fn ann(x, t) {
  c.Term(c.Ann(x, t), s())
}

fn app(f, a) {
  c.Term(c.App(f, a), s())
}

fn match(arg, cases) {
  c.Term(c.Match(arg, cases), s())
}

fn err(e) {
  c.Term(c.Err(e), s())
}
