import core/ast.{
  type Case, type Pattern, type Span, type Term, type Value, Ann, App, Case, Ctr,
  HVar, Hole, Lam, Match, PAny, PCtr, PVar, Pi, Span, Term, Typ, VCtr, VLam,
  VNeut, VPi, VTyp, Var,
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

fn var(i) {
  Term(Var(i), s())
}

fn pi(n, d, c) {
  Term(Pi(n, d, c), s())
}

fn lam(n, b) {
  Term(Lam(n, b), s())
}

fn app(f, a) {
  Term(App(f, a), s())
}

fn ann(x, t) {
  Term(Ann(x, t), s())
}

fn ctr(k, args) {
  Term(Ctr(k, args), s())
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

pub fn var_eval_test() {
  eval.eval([], var(0)) |> should.equal(VNeut(HVar(0), []))
  eval.eval([], var(1)) |> should.equal(VNeut(HVar(1), []))
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
  eval_pi([], "x", typ(1), typ(2))
  |> should.equal(VCtr("x", [VTyp(1), VTyp(2)]))
  eval_pi([], "y", typ(1), var(0))
  |> should.equal(VCtr("y", [VTyp(1), VTyp(42)]))
  eval_pi([], "z", typ(1), var(1))
  |> should.equal(VCtr("z", [VTyp(1), VNeut(HVar(1), [])]))
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
  eval_lam([], "x", typ(1)) |> should.equal(VCtr("x", [VTyp(1)]))
  eval_lam([], "x", var(0)) |> should.equal(VCtr("x", [VTyp(42)]))
  eval_lam([], "x", var(1)) |> should.equal(VCtr("x", [VNeut(HVar(1), [])]))
}

pub fn identity_function_test() {
  // (\x. x) y  ->  y
  // In De Bruijn: (\. 0) applied to (Var 99)
  let id = lam("x", var(0))
  let expr = app(id, var(99))
  case eval.eval([], expr) {
    ast.VNeut(ast.HVar(99), []) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn const_function_test() {
  // (\x. \y. x) a b -> a
  // In De Bruijn: (\. \. 1) applied to a, then b
  let const_fn = lam("x", lam("y", var(1)))
  let a = var(10)
  let b = var(20)
  let expr = app(app(const_fn, a), b)

  let result = eval.eval([], expr)

  // Expect: a (which is Var 10)
  case result {
    ast.VNeut(ast.HVar(10), []) -> True
    _ -> False
  }
  |> should.be_true
}

pub fn pattern_match_eval_test() {
  // match Just(A) { 
  //   Nothing -> B 
  //   Just(x) -> x 
  // }
  // Should evaluate to A

  let val_a = var(100)
  let val_b = var(200)

  let just_a = ctr("Just", [val_a])

  let case_nothing = Case(pattern: PCtr("Nothing", []), body: val_b, span: s())

  let case_just =
    Case(
      pattern: PCtr("Just", [PVar("x")]),
      body: var(0),
      // x is bound at index 0 in this scope
      span: s(),
    )

  let expr = Term(Match(just_a, [case_nothing, case_just]), s())

  let result = eval.eval([], expr)

  // Expect: val_a (Var 100)
  case result {
    ast.VNeut(ast.HVar(100), []) -> True
    _ -> False
  }
  |> should.be_true
}
