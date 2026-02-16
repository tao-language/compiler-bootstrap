import core/ast.{
  type Case, type Pattern, type Span, type Term, type Value, Ann, App, Case, Ctr,
  HVar, Hole, I32, I32T, Lam, Lit, LitT, Match, PAny, PCtr, PVar, Pi, Span, Term,
  Typ, VCtr, VErr, VLam, VLit, VLitT, VNeut, VPi, VTyp, Var,
}
import core/eval
import gleam/option.{Some}
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// --- HELPERS to make writing ASTs less painful ---
fn s() {
  Span(0, 0, "test")
}

fn typ(i) {
  Term(Typ(i), s())
}

fn lit(v) {
  Term(Lit(v), s())
}

fn lit_t(t) {
  Term(LitT(t), s())
}

fn var(i) {
  Term(Var(i), s())
}

fn pi(n, d, c) {
  Term(Pi(n, d, c), s())
}

fn lam(n, b) {
  Term(Lam(n, b), s())
}

fn ann(x, t) {
  Term(Ann(x, t), s())
}

fn ctr(k, args) {
  Term(Ctr(k, args), s())
}

fn app(f, a) {
  Term(App(f, a), s())
}

fn match(arg, cases) {
  Term(Match(arg, cases), s())
}

fn hole() {
  Term(Hole, s())
}

pub fn env_get_test() {
  let a = VTyp(0)
  let b = VTyp(1)
  eval.env_get([], 0) |> should.be_none
  eval.env_get([a], 0) |> should.equal(Some(a))
  eval.env_get([a, b], 0) |> should.equal(Some(a))
  eval.env_get([a, b], 1) |> should.equal(Some(b))
}

pub fn typ_eval_test() {
  eval.eval([], typ(0)) |> should.equal(VTyp(0))
  eval.eval([], typ(1)) |> should.equal(VTyp(1))
}

pub fn lit_eval_test() {
  eval.eval([], lit(I32(42))) |> should.equal(VLit(I32(42)))
}

pub fn lit_t_eval_test() {
  eval.eval([], lit_t(I32T)) |> should.equal(VLitT(I32T))
}

pub fn var_eval_test() {
  // eval.eval([], var(0)) |> should.equal(VNeut(HVar(0), []))
  eval.eval([], var(0)) |> should.equal(VErr(ast.UnboundVar(0, s())))
  eval.eval([VTyp(1)], var(0)) |> should.equal(VTyp(1))
}

pub fn pi_eval_test() {
  // Since we can't compare the closure directly, resolve it first.
  // Capture it into a VCtr to get the name, input, and output.
  let eval_pi = fn(env, name, input, output) {
    case eval.eval(env, pi(name, input, output)) {
      VPi(x, input, output) -> VCtr(x, [input, output(VTyp(42))])
      value -> value
    }
  }
  eval_pi([], "a", typ(1), typ(2))
  |> should.equal(VCtr("a", [VTyp(1), VTyp(2)]))
  eval_pi([], "b", typ(1), var(0))
  |> should.equal(VCtr("b", [VTyp(1), VTyp(42)]))
  eval_pi([], "c", typ(1), var(1))
  |> should.equal(VCtr("c", [VTyp(1), VErr(ast.UnboundVar(1, s()))]))
}

pub fn lam_eval_test() {
  // Since we can't compare the closure directly, resolve it first.
  // Capture it into a VCtr to get the name and output.
  let eval_lam = fn(env, name, output) {
    case eval.eval(env, lam(name, output)) {
      VLam(x, output) -> VCtr(x, [output(VTyp(42))])
      value -> value
    }
  }
  eval_lam([], "a", typ(1)) |> should.equal(VCtr("a", [VTyp(1)]))
  eval_lam([], "b", var(0)) |> should.equal(VCtr("b", [VTyp(42)]))
  eval_lam([], "c", var(1))
  |> should.equal(VCtr("c", [VErr(ast.UnboundVar(1, s()))]))
}

pub fn ann_eval_test() {
  let env = [VTyp(42)]
  eval.eval(env, ann(var(0), typ(1))) |> should.equal(VTyp(42))
}

pub fn ctr_eval_test() {
  let env = [VTyp(42)]
  eval.eval(env, ctr("A", [var(0)])) |> should.equal(VCtr("A", [VTyp(42)]))
}

pub fn app_eval_test() {
  let env = [VLam("a", fn(x) { x })]
  eval.eval(env, app(typ(0), typ(42)))
  |> should.equal(VErr(ast.NotAFunction(VTyp(0), s())))
  eval.eval(env, app(var(0), typ(42)))
  |> should.equal(VTyp(42))
  eval.eval(env, app(var(1), typ(42)))
  |> should.equal(VErr(ast.NotAFunction(VErr(ast.UnboundVar(1, s())), s())))
  case eval.eval(env, app(pi("a", typ(0), typ(1)), typ(42))) {
    VErr(ast.NotAFunction(_, _)) -> True
    _ -> False
  }
  |> should.equal(True)
  eval.eval(env, app(lam("a", var(0)), typ(42)))
  |> should.equal(VTyp(42))
  eval.eval(env, app(ann(var(0), typ(1)), typ(42)))
  |> should.equal(VTyp(42))
  eval.eval(env, app(ctr("A", [typ(1)]), typ(42)))
  |> should.equal(VErr(ast.NotAFunction(VCtr("A", [VTyp(1)]), s())))
}

pub fn match_eval_test() {
  let i1 = lit(I32(1))
  let i2 = lit(I32(2))
  match(ctr("Just", [i1]), [
    Case(PCtr("Nothing", []), i2, s()),
    Case(PCtr("Just", [PVar("x")]), var(0), s()),
  ])
  |> eval.eval([], _)
  |> should.equal(VLit(I32(1)))

  match(ctr("Nothing", []), [
    Case(PCtr("Nothing", []), i2, s()),
    Case(PCtr("Just", [PVar("x")]), var(0), s()),
  ])
  |> eval.eval([], _)
  |> should.equal(VLit(I32(2)))

  match(ctr("Null", []), [
    Case(PCtr("Nothing", []), i2, s()),
    Case(PCtr("Just", [PVar("x")]), var(0), s()),
  ])
  |> eval.eval([], _)
  |> should.equal(VErr(ast.MatchUnhandledCase(VCtr("Null", []), s())))
}

pub fn hole_eval_test() {
  eval.eval([], hole()) |> should.equal(VErr(ast.EvalHole(s())))
}
