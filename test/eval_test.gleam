import core/ast.{
  App, Case, Constructor, Lam, Match, PConstructor, PVar, Span, Term, Universe,
  Var,
}
import core/eval
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// --- HELPERS to make writing ASTs less painful ---
fn s() {
  Span(0, 0, "test")
}

// Dummy span

fn var(i) {
  Term(Var(i), s())
}

fn univ(i) {
  Term(Universe(i), s())
}

fn lam(n, b) {
  Term(Lam(n, b), s())
}

fn app(f, a) {
  Term(App(f, a), s())
}

fn con(n, args) {
  Term(Constructor(n, args), s())
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

  let just_a = con("Just", [val_a])

  let case_nothing =
    Case(pattern: PConstructor("Nothing", []), body: val_b, span: s())

  let case_just =
    Case(
      pattern: PConstructor("Just", [PVar("x")]),
      body: var(0),
      // x is bound at index 0 in this scope
      span: s(),
    )

  let expr = Term(Match(just_a, [case_nothing, case_just]), s())

  let result = eval.eval([], expr)
  echo result

  // Expect: val_a (Var 100)
  case result {
    ast.VNeut(ast.HVar(100), []) -> True
    _ -> False
  }
  |> should.be_true
}
