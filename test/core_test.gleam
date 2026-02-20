import core as c
import gleeunit
import gleeunit/should

// TODO: test unify
// TODO: test quote
// TODO: test normalize

pub fn main() {
  gleeunit.main()
}

pub fn range_test() {
  c.range(0, 0, 1) |> should.equal([])
  c.range(0, 1, 1) |> should.equal([0])
  c.range(0, 2, 1) |> should.equal([0, 1])
  c.range(0, 3, 1) |> should.equal([0, 1, 2])
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
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(1), c.VTyp(2), s)))
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

  c.check(0, [], [], [], lit(c.I32(1)), c.VLitT(c.I64T))
  |> should.equal(c.VErr(c.TypeMismatch(c.VLitT(c.I32T), c.VLitT(c.I64T), s)))
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
  c.check(0, [], [], [], lit_t(c.I32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.I64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.U32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.U64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.F32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], lit_t(c.F64T), c.VTyp(0)) |> should.equal(c.VTyp(0))

  c.check(0, [], [], [], lit_t(c.I32T), c.VTyp(1))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s)))
}

// --- Var --- \\
pub fn var_eval_test() {
  let env = [c.VTyp(0)]
  c.eval(env, var(0)) |> should.equal(c.VTyp(0))
  c.eval(env, var(1)) |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_infer_test() {
  let ctx = [#("x", c.VTyp(0))]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(c.VTyp(0))
  c.infer(0, ctx, [], [], var(1))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_check_test() {
  let ctx = [#("x", c.VTyp(0))]
  c.check(0, ctx, [], [], var(0), c.VTyp(0)) |> should.equal(c.VTyp(0))

  c.check(0, ctx, [], [], var(1), c.VTyp(0))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
  c.check(0, ctx, [], [], var(0), c.VTyp(1))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s)))
}

// --- Ctr --- \\
pub fn ctr_eval_test() {
  c.eval([], ctr("A", [])) |> should.equal(c.VCtr("A", []))
  c.eval([], ctr("A", [typ(0)])) |> should.equal(c.VCtr("A", [c.VTyp(0)]))
  c.eval([], ctr("A", [typ(0), typ(1)]))
  |> should.equal(c.VCtr("A", [c.VTyp(0), c.VTyp(1)]))
}

pub fn ctr_infer_test() {
  c.infer(0, [], [], [], ctr("A", []))
  |> should.equal(c.VErr(c.TypeAnnotationNeeded(ctr("A", []))))
}

pub fn ctr_check_test() {
  let tenv = []
  c.check(0, [], [], tenv, ctr("Undefined", []), c.VTyp(0))
  |> should.equal(c.VErr(c.CtrUndefined("Undefined", s)))

  let tenv = [#("Ctr0", c.CtrDef([], [], typ(0)))]
  c.check(0, [], [], tenv, ctr("Ctr0", []), c.VTyp(0))
  |> should.equal(c.VTyp(0))

  let tenv = [#("Ctr0", c.CtrDef([], [], typ(1)))]
  c.check(0, [], [], tenv, ctr("Ctr0", []), c.VTyp(0))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(1), c.VTyp(0), s)))

  let tenv = [#("UndefVarInCtr", c.CtrDef([], [var(0)], var(0)))]
  c.check(0, [], [], tenv, ctr("UndefVarInCtr", [typ(0)]), c.VTyp(0))
  |> should.equal(c.VErr(c.VarUndefined(0, s)))

  let tenv = [#("Ctr1", c.CtrDef(["a"], [var(0)], var(0)))]
  c.check(0, [], [], tenv, ctr("Ctr1", [typ(0)]), c.VTyp(1))
  |> should.equal(c.VTyp(1))

  let ctr_def = c.CtrDef(["a"], [var(0)], var(0))
  let tenv = [#("TooFewArgs", ctr_def)]
  c.check(0, [], [], tenv, ctr("TooFewArgs", []), c.VTyp(1))
  |> should.equal(
    c.VBad(c.VTyp(1), [
      c.CtrTooFewArgs("TooFewArgs", [], ctr_def, s),
    ]),
  )
  let ctr_def = c.CtrDef(["a"], [], var(0))
  let tenv = [#("TooManyArgs", ctr_def)]
  c.check(0, [], [], tenv, ctr("TooManyArgs", [typ(0)]), c.VTyp(0))
  |> should.equal(
    c.VBad(c.VTyp(0), [
      c.CtrTooManyArgs("TooManyArgs", [typ(0)], ctr_def, s),
    ]),
  )

  let ctr_def = c.CtrDef(["a", "b"], [var(0), var(1)], var(0))
  let tenv = [#("Unsolved", ctr_def)]
  c.check(0, [], [], tenv, ctr("Unsolved", [typ(0), typ(1)]), c.VTyp(1))
  |> should.equal(
    c.VBad(c.VTyp(1), [
      c.CtrUnsolvedParam("Unsolved", [typ(0), typ(1)], ctr_def, id: 1, span: s),
    ]),
  )

  let ctr_def =
    c.CtrDef(["a", "b"], [var(0), var(1)], ctr("T", [var(0), var(1)]))
  let tenv = [#("Ctr2", ctr_def)]
  let term = ctr("Ctr2", [typ(0), typ(1)])
  let ty = c.VCtr("T", [c.VTyp(1), c.VTyp(2)])
  c.check(0, [], [], tenv, term, ty)
  |> should.equal(ty)
}

// --- Ann --- \\
pub fn ann_eval_test() {
  let env = [c.VTyp(42)]
  c.eval(env, ann(var(0), typ(1))) |> should.equal(c.VTyp(42))
}

pub fn ann_infer_test() {
  c.infer(0, [], [], [], ann(lit(c.I32(1)), lit_t(c.I32T)))
  |> should.equal(c.VLitT(c.I32T))

  c.infer(0, [], [], [], ann(lit_t(c.I32T), lit(c.I32(1))))
  |> should.equal(
    c.VBad(c.VErr(c.TypeMismatch(c.VTyp(0), c.VLit(c.I32(1)), s)), [
      c.AnnNotType(lit(c.I32(1)), c.VLitT(c.I32T)),
    ]),
  )

  c.infer(0, [], [], [], ann(typ(0), typ(1)))
  |> should.equal(c.VTyp(1))

  c.infer(0, [], [], [], ann(typ(1), typ(0)))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(0), s)))
}

pub fn ann_check_test() {
  c.check(0, [], [], [], ann(typ(0), typ(1)), c.VTyp(1))
  |> should.equal(c.VTyp(1))

  c.check(0, [], [], [], ann(typ(0), typ(1)), c.VTyp(0))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(1), c.VTyp(0), s)))
}

// --- Lam --- \\
pub fn lam_eval_test() {
  c.eval([], lam("x", var(0)))
  |> should.equal(c.VLam("x", [], var(0)))
}

pub fn lam_infer_test() {
  c.infer(0, [], [], [], lam("x", var(0)))
  |> should.equal(c.VErr(c.TypeAnnotationNeeded(lam("x", var(0)))))
}

pub fn lam_check_test() {
  let ty = c.VPi("x", [], c.VTyp(0), typ(0))
  c.check(0, [], [], [], lam("x", var(0)), ty)
  |> should.equal(ty)

  c.check(0, [], [], [], lam("y", var(0)), c.VTyp(0))
  |> should.equal(c.VErr(c.TypeAnnotationNeeded(lam("y", var(0)))))
}

// --- Pi --- \\
pub fn pi_eval_test() {
  c.eval([], pi("x", typ(0), var(0)))
  |> should.equal(c.VPi("x", [], c.VTyp(0), var(0)))
}

pub fn pi_infer_test() {
  c.infer(0, [], [], [], pi("x", typ(0), var(0)))
  |> should.equal(c.VTyp(0))

  c.infer(0, [], [], [], pi("y", lit(c.I32(1)), var(0)))
  |> should.equal(
    c.VBad(c.VTyp(0), [c.PiInputNotType(lit(c.I32(1)), c.VLitT(c.I32T))]),
  )
}

pub fn pi_check_test() {
  let term = pi("x", typ(0), typ(1))
  c.check(0, [], [], [], term, c.VTyp(0))
  |> should.equal(c.VTyp(0))

  c.check(0, [], [], [], term, c.VTyp(1))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s)))
}

// --- App --- \\
pub fn app_eval_test() {
  let env = [c.VLam("a", [], var(0))]
  c.eval(env, app(typ(0), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VTyp(0), s)))
  c.eval(env, app(var(0), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(var(1), typ(42)))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
  c.eval(env, app(pi("a", typ(0), typ(1)), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VPi("a", env, c.VTyp(0), typ(1)), s)))
  c.eval(env, app(lam("a", var(0)), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(ann(var(0), typ(1)), typ(42)))
  |> should.equal(c.VTyp(42))
  c.eval(env, app(ctr("A", [typ(1)]), typ(42)))
  |> should.equal(c.VErr(c.NotAFunction(c.VCtr("A", [c.VTyp(1)]), s)))
}

// --- Match --- \\
pub fn match_eval_test() {
  let i1 = lit(c.I32(1))
  let i2 = lit(c.I32(2))
  match(ctr("Just", [i1]), [
    c.Case(c.PCtr("Nothing", []), i2, s),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s),
  ])
  |> c.eval([], _)
  |> should.equal(c.VLit(c.I32(1)))

  match(ctr("Nothing", []), [
    c.Case(c.PCtr("Nothing", []), i2, s),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s),
  ])
  |> c.eval([], _)
  |> should.equal(c.VLit(c.I32(2)))

  match(ctr("Null", []), [
    c.Case(c.PCtr("Nothing", []), i2, s),
    c.Case(c.PCtr("Just", [c.PVar("x")]), var(0), s),
  ])
  |> c.eval([], _)
  |> should.equal(c.VErr(c.MatchUnhandledCase(c.VCtr("Null", []), s)))
}

// --- Bad --- \\
// TODO

// --- Err --- \\
// TODO

// --- HELPERS to make writing ASTs less painful ---
const s = c.Span("core_test", 1, 1)

fn typ(l) {
  c.Term(c.Typ(l), s)
}

fn lit(v) {
  c.Term(c.Lit(v), s)
}

fn lit_t(t) {
  c.Term(c.LitT(t), s)
}

fn var(i) {
  c.Term(c.Var(i), s)
}

fn ctr(k, args) {
  c.Term(c.Ctr(k, args), s)
}

fn pi(name, in, out) {
  c.Term(c.Pi(name, in, out), s)
}

fn lam(name, body) {
  c.Term(c.Lam(name, body), s)
}

fn ann(x, t) {
  c.Term(c.Ann(x, t), s)
}

fn app(f, a) {
  c.Term(c.App(f, a), s)
}

fn match(arg, cases) {
  c.Term(c.Match(arg, cases), s)
}

fn err(e) {
  c.Term(c.Err(e), s)
}
