import core/ast
import core/eval.{eval}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s0 = Span("eval_test", 0, 0, 0, 0)

const s1 = Span("eval_test", 1, 1, 1, 1)

const s2 = Span("eval_test", 2, 2, 2, 2)

const s3 = Span("eval_test", 3, 3, 3, 3)

const s4 = Span("eval_test", 4, 4, 4, 4)

const s5 = Span("eval_test", 5, 5, 5, 5)

const s6 = Span("eval_test", 6, 6, 6, 6)

const s7 = Span("eval_test", 7, 7, 7, 7)

const s8 = Span("eval_test", 8, 8, 8, 8)

pub fn eval_typ_test() {
  let term = ast.Typ(0, s0)
  let result = eval([], [], term)
  assert result == ast.VTyp(0)
}

pub fn eval_hole_test() {
  let term = ast.Hole(0, s0)
  let result = eval([], [], term)
  assert result == ast.vhole(0, [])
}

pub fn eval_lit_test() {
  let term = ast.Lit(ast.Int(1), s0)
  let result = eval([], [], term)
  assert result == ast.vint(1)
}

pub fn eval_litt_test() {
  let term = ast.LitT(ast.IntT, s0)
  let result = eval([], [], term)
  assert result == ast.vint_t
}

pub fn eval_var_undefined_test() {
  let term = ast.Var(0, s0)
  let result = eval([], [], term)
  assert result == ast.VErr
}

pub fn eval_var0_test() {
  let term = ast.Var(0, s0)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vint_t
}

pub fn eval_var1_test() {
  let term = ast.Var(1, s0)
  let env = [ast.vint_t, ast.vfloat_t]
  let result = eval([], env, term)
  assert result == ast.vfloat_t
}

pub fn eval_ctr_test() {
  let term = ast.Ctr("A", ast.int_t(s1), s0)
  let result = eval([], [], term)
  assert result == ast.VCtr("A", ast.vint_t)
}
// Ctr(tag: String, arg: Term, span: Span)
// Rcd(fields: List(#(String, Term)), span: Span)
// RcdT(fields: List(#(String, Term, Option(Term))), span: Span)
// Call(name: String, args: List(#(Term, Term)), return_type: Term, span: Span)
// TypeDef(
// Ann(term: Term, type_: Term, span: Span)
// Lam(
// Pi(
// Fix(name: String, body: Term, span: Span)
// App(fun: Term, arg: Term, span: Span)
// Match(arg: Term, cases: List(Case), span: Span)
// Err(message: String, span: Span)
