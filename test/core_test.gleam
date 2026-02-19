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
  c.infer(0, [], [], [], typ(0)) |> should.equal(c.VTyp(1))
}

pub fn typ_check_test() {
  c.check(0, [], [], [], typ(0), c.VTyp(1)) |> should.equal(c.VTyp(1))
  c.check(0, [], [], [], typ(0), c.VTyp(2))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(1), c.VTyp(2), s())))
}

// --- Lit --- \\
pub fn lit_eval_test() {
  c.eval([], lit(c.I32(1))) |> should.equal(c.VLit(c.I32(1)))
  c.eval([], lit(c.I64(1))) |> should.equal(c.VLit(c.I64(1)))
  c.eval([], lit(c.U32(1))) |> should.equal(c.VLit(c.U32(1)))
  c.eval([], lit(c.U64(1))) |> should.equal(c.VLit(c.U64(1)))
  c.eval([], lit(c.F32(1.0))) |> should.equal(c.VLit(c.F32(1.0)))
  c.eval([], lit(c.F64(1.0))) |> should.equal(c.VLit(c.F64(1.0)))
}

pub fn lit_infer_test() {
  c.infer(0, [], [], [], lit(c.I32(1))) |> should.equal(c.VLitT(c.I32T))
  c.infer(0, [], [], [], lit(c.I64(1))) |> should.equal(c.VLitT(c.I64T))
  c.infer(0, [], [], [], lit(c.U32(1))) |> should.equal(c.VLitT(c.U32T))
  c.infer(0, [], [], [], lit(c.U64(1))) |> should.equal(c.VLitT(c.U64T))
  c.infer(0, [], [], [], lit(c.F32(1.0))) |> should.equal(c.VLitT(c.F32T))
  c.infer(0, [], [], [], lit(c.F64(1.0))) |> should.equal(c.VLitT(c.F64T))
}

pub fn lit_check_test() {
  c.check(0, [], [], [], lit(c.I32(1)), c.VLitT(c.I32T))
  |> should.equal(c.VLitT(c.I32T))
  c.check(0, [], [], [], lit(c.I64(1)), c.VLitT(c.I64T))
  |> should.equal(c.VLitT(c.I64T))
  c.check(0, [], [], [], lit(c.U32(1)), c.VLitT(c.U32T))
  |> should.equal(c.VLitT(c.U32T))
  c.check(0, [], [], [], lit(c.U64(1)), c.VLitT(c.U64T))
  |> should.equal(c.VLitT(c.U64T))
  c.check(0, [], [], [], lit(c.F32(1.0)), c.VLitT(c.F32T))
  |> should.equal(c.VLitT(c.F32T))
  c.check(0, [], [], [], lit(c.F64(1.0)), c.VLitT(c.F64T))
  |> should.equal(c.VLitT(c.F64T))
}

// --- LitT --- \\
pub fn lit_t_eval_test() {
  c.eval([], lit_t(c.I32T)) |> should.equal(c.VLitT(c.I32T))
  c.eval([], lit_t(c.I64T)) |> should.equal(c.VLitT(c.I64T))
  c.eval([], lit_t(c.U32T)) |> should.equal(c.VLitT(c.U32T))
  c.eval([], lit_t(c.U64T)) |> should.equal(c.VLitT(c.U64T))
  c.eval([], lit_t(c.F32T)) |> should.equal(c.VLitT(c.F32T))
  c.eval([], lit_t(c.F64T)) |> should.equal(c.VLitT(c.F64T))
}

pub fn lit_t_infer_test() {
  c.infer(0, [], [], [], lit_t(c.I32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], lit_t(c.I64T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], lit_t(c.U32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], lit_t(c.U64T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], lit_t(c.F32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], lit_t(c.F64T)) |> should.equal(c.VTyp(0))
}

pub fn lit_t_check_test() {
  c.check(0, [], [], [], lit_t(c.I32T), c.VTyp(1))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s())))
  c.check(0, [], [], [], lit_t(c.I32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.I64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.U32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.U64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.F32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.F64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
}

// --- Var --- \\
pub fn var_eval_test() {
  // c.eval([], var(0)) |> should.equal(VNeut(HVar(0), []))
  c.eval([], var(0)) |> should.equal(c.VErr(c.UnboundVar(0, s())))
  c.eval([c.VTyp(1)], var(0)) |> should.equal(c.VTyp(1))
}

pub fn var_infer_test() {
  let ctx = [#("x", c.VTyp(0))]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(c.VTyp(0))
  c.infer(0, ctx, [], [], var(1))
  |> should.equal(c.VErr(c.UnboundVar(1, s())))
}

pub fn var_check_test() {
  let ctx = [#("x", c.VTyp(0))]
  c.check(0, ctx, [], [], var(0), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, ctx, [], [], var(1), c.VTyp(0))
  |> should.equal(c.VErr(c.UnboundVar(1, s())))
}

// --- Ctr --- \\
pub fn ctr_eval_test() {
  let env = [c.VTyp(42)]
  c.eval(env, ctr("A", [var(0)])) |> should.equal(c.VCtr("A", [c.VTyp(42)]))
}

pub fn ctr_infer_test() {
  c.infer(0, [], [], [], ctr("A", []))
  |> should.equal(c.VErr(c.TypeAnnotationNeeded(ctr("A", []))))
}

pub fn ctr_check_test() {
  todo
}

// --- Ann --- \\
pub fn ann_eval_test() {
  let env = [c.VTyp(42)]
  c.eval(env, ann(var(0), typ(1))) |> should.equal(c.VTyp(42))
}

// --- Lam --- \\
pub fn lam_eval_test() {
  c.eval([], lam("x", var(0)))
  |> should.equal(c.VLam("x", [], var(0)))
}

// --- Pi --- \\
pub fn pi_eval_test() {
  c.eval([], pi("x", typ(0), var(0)))
  |> should.equal(c.VPi("x", [], c.VTyp(0), var(0)))
}

// --- App --- \\
pub fn app_eval_test() {
  let env = [c.VLam("a", [], var(0))]
  c.eval(env, app(typ(0), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VTyp(0), s())))
  c.eval(env, app(var(0), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(var(1), typ(42)))
  |> should.equal(c.VErr(c.UnboundVar(1, s())))
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
