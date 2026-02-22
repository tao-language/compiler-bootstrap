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

  c.check(0, [], [], [], typ(1), c.VTyp(0))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(0), s)))
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
pub fn litt_eval_test() {
  c.eval([], litt(c.I32T)) |> should.equal(c.VLitT(c.I32T))
  c.eval([], litt(c.I64T)) |> should.equal(c.VLitT(c.I64T))
  c.eval([], litt(c.U32T)) |> should.equal(c.VLitT(c.U32T))
  c.eval([], litt(c.U64T)) |> should.equal(c.VLitT(c.U64T))
  c.eval([], litt(c.F32T)) |> should.equal(c.VLitT(c.F32T))
  c.eval([], litt(c.F64T)) |> should.equal(c.VLitT(c.F64T))
}

pub fn litt_infer_test() {
  c.infer(0, [], [], [], litt(c.I32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], litt(c.I64T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], litt(c.U32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], litt(c.U64T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], litt(c.F32T)) |> should.equal(c.VTyp(0))
  c.infer(0, [], [], [], litt(c.F64T)) |> should.equal(c.VTyp(0))
}

pub fn litt_check_test() {
  c.check(0, [], [], [], litt(c.I32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.I64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.U32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.U64T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.F32T), c.VTyp(0)) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.F64T), c.VTyp(0)) |> should.equal(c.VTyp(0))

  c.check(0, [], [], [], litt(c.I32T), c.VTyp(1))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s)))
}

// --- Var --- \\
pub fn var_eval_test() {
  let env = [v32(0)]
  c.eval(env, var(0)) |> should.equal(v32(0))
  c.eval(env, var(1)) |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_infer_test() {
  let ctx = [#("x", v32t)]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(v32t)
  c.infer(0, ctx, [], [], var(1))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_check_test() {
  let ctx = [#("x", v32t)]
  c.check(0, ctx, [], [], var(0), v32t) |> should.equal(v32t)

  c.check(0, ctx, [], [], var(1), v32t)
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
  c.check(0, ctx, [], [], var(0), v64t)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s)))
}

// --- Ctr --- \\
pub fn ctr_eval_test() {
  c.eval([], ctr("A", [])) |> should.equal(c.VCtr("A", []))
  c.eval([], ctr("A", [i32(0)])) |> should.equal(c.VCtr("A", [v32(0)]))
  c.eval([], ctr("A", [i32(0), i32(1)]))
  |> should.equal(c.VCtr("A", [v32(0), v32(1)]))
}

pub fn ctr_infer_test() {
  c.infer(0, [], [], [], ctr("A", []))
  |> should.equal(c.VErr(c.TypeAnnotationNeeded(ctr("A", []))))
}

pub fn ctr_check_test() {
  let tenv = []
  c.check(0, [], [], tenv, ctr("Undefined", []), v32t)
  |> should.equal(c.VErr(c.CtrUndefined("Undefined", s)))

  let tenv = [#("Ctr0", c.CtrDef([], [], i32t))]
  c.check(0, [], [], tenv, ctr("Ctr0", []), v32t)
  |> should.equal(v32t)
  c.check(0, [], [], tenv, ctr("Ctr0", []), v64t)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s)))

  let tenv = [#("UndefVarInCtr", c.CtrDef([], [var(0)], var(0)))]
  c.check(0, [], [], tenv, ctr("UndefVarInCtr", [i32(1)]), c.VTyp(0))
  |> should.equal(c.VErr(c.VarUndefined(0, s)))

  let tenv = [#("Ctr1", c.CtrDef(["a"], [var(0)], var(0)))]
  c.check(0, [], [], tenv, ctr("Ctr1", [i32(1)]), v32t)
  |> should.equal(v32t)

  let ctr_def = c.CtrDef(["a"], [var(0)], var(0))
  let tenv = [#("TooFewArgs", ctr_def)]
  c.check(0, [], [], tenv, ctr("TooFewArgs", []), v32t)
  |> should.equal(c.VBad(v32t, [c.CtrTooFewArgs("TooFewArgs", [], ctr_def, s)]))

  let ctr_def = c.CtrDef(["a"], [], var(0))
  let tenv = [#("TooManyArgs", ctr_def)]
  c.check(0, [], [], tenv, ctr("TooManyArgs", [i32(1)]), v32t)
  |> should.equal(
    c.VBad(v32t, [c.CtrTooManyArgs("TooManyArgs", [i32(1)], ctr_def, s)]),
  )

  let ctr_def = c.CtrDef(["a", "b"], [var(0), var(1)], var(0))
  let tenv = [#("Unsolved", ctr_def)]
  c.check(0, [], [], tenv, ctr("Unsolved", [i32(1), i32(2)]), v32t)
  |> should.equal(
    c.VBad(v32t, [
      c.CtrUnsolvedParam("Unsolved", [i32(1), i32(2)], ctr_def, id: 1, span: s),
    ]),
  )

  let ctr_def =
    c.CtrDef(["a", "b"], [var(0), var(1)], ctr("T", [var(0), var(1)]))
  let tenv = [#("Ctr2", ctr_def)]
  let term = ctr("Ctr2", [i32(1), i64(2)])
  let ty = c.VCtr("T", [v32t, v64t])
  c.check(0, [], [], tenv, term, ty) |> should.equal(ty)
}

// --- Rcd --- \\
pub fn rcd_eval_test() {
  c.eval([], rcd([])) |> should.equal(c.VRcd([]))
  c.eval([], rcd([#("a", i32(1))]))
  |> should.equal(c.VRcd([#("a", v32(1))]))
  c.eval([], rcd([#("a", i32(1)), #("b", i64(2))]))
  |> should.equal(c.VRcd([#("a", v32(1)), #("b", v64(2))]))
}

pub fn rcd_infer_test() {
  c.infer(0, [], [], [], rcd([])) |> should.equal(c.VRcd([]))
  c.infer(0, [], [], [], rcd([#("a", i32(1))]))
  |> should.equal(c.VRcd([#("a", v32t)]))
  c.infer(0, [], [], [], rcd([#("a", i32(1)), #("b", i64(2))]))
  |> should.equal(c.VRcd([#("a", v32t), #("b", v64t)]))
}

pub fn rcd_check_test() {
  c.check(0, [], [], [], rcd([]), c.VRcd([])) |> should.equal(c.VRcd([]))
  c.check(0, [], [], [], rcd([#("a", i32(1))]), c.VRcd([#("a", v32t)]))
  |> should.equal(c.VRcd([#("a", v32t)]))
  let ty = c.VRcd([#("a", v32t), #("b", v64t)])
  c.check(0, [], [], [], rcd([#("a", i32(1)), #("b", i64(2))]), ty)
  |> should.equal(ty)
  c.check(0, [], [], [], rcd([#("b", i64(2)), #("a", i32(1))]), ty)
  |> should.equal(ty)
}

// --- Dot --- \\
pub fn dot_eval_test() {
  c.eval([], dot(i32(1), "a"))
  |> should.equal(c.VErr(c.DotOnNonRecord(v32(1), "a", s)))
  c.eval([], dot(rcd([]), "a"))
  |> should.equal(c.VErr(c.DotNotFound("a", [], s)))
  c.eval([], dot(rcd([#("a", i32(1)), #("b", i64(2))]), "a"))
  |> should.equal(v32(1))
  c.eval([], dot(rcd([#("a", i32(1)), #("b", i64(2))]), "b"))
  |> should.equal(v64(2))
  c.eval([c.VNeut(c.HVar(0), [])], dot(var(0), "a"))
  |> should.equal(c.VNeut(c.HVar(0), [c.EDot("a")]))
}

pub fn dot_infer_test() {
  c.infer(0, [], [], [], dot(i32(1), "a"))
  |> should.equal(c.VErr(c.DotOnNonRecord(v32t, "a", s)))
  c.infer(0, [], [], [], dot(rcd([]), "a"))
  |> should.equal(c.VErr(c.DotNotFound("a", [], s)))
  c.infer(0, [], [], [], dot(rcd([#("a", i32(1)), #("b", i64(2))]), "a"))
  |> should.equal(v32t)
  c.infer(0, [], [], [], dot(rcd([#("a", i32(1)), #("b", i64(2))]), "b"))
  |> should.equal(v64t)
}

pub fn dot_check_test() {
  let record = rcd([#("a", i32(1)), #("b", i64(2))])
  c.check(0, [], [], [], dot(record, "a"), v32t)
  |> should.equal(v32t)
  c.check(0, [], [], [], dot(record, "b"), v64t)
  |> should.equal(v64t)
}

// --- Ann --- \\
pub fn ann_eval_test() {
  let env = [v32(1)]
  c.eval(env, ann(var(0), typ(1))) |> should.equal(v32(1))
}

pub fn ann_infer_test() {
  c.infer(0, [], [], [], ann(i32(1), i32t))
  |> should.equal(v32t)

  c.infer(0, [], [], [], ann(i32t, i32(1)))
  |> should.equal(
    c.VBad(c.VErr(c.TypeMismatch(c.VTyp(0), v32(1), s)), [
      c.NotType(i32(1), v32t),
    ]),
  )

  c.infer(0, [], [], [], ann(typ(0), typ(1)))
  |> should.equal(c.VTyp(1))

  c.infer(0, [], [], [], ann(typ(1), typ(0)))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(0), s)))
}

pub fn ann_check_test() {
  c.check(0, [], [], [], ann(i32(1), i32t), v32t)
  |> should.equal(v32t)

  c.check(0, [], [], [], ann(i32(1), i32t), v64t)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s)))
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

  c.infer(0, [], [], [], pi("y", i32(1), var(0)))
  |> should.equal(c.VBad(c.VTyp(0), [c.NotType(i32(1), v32t)]))
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
  c.eval([], app(typ(0), typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(c.VTyp(0), s)))
  c.eval([], app(i32(1), typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(v32(1), s)))
  c.eval([], app(i32t, typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(v32t, s)))
  let env = [c.VLam("a", [], var(0))]
  c.eval(env, app(var(0), typ(1)))
  |> should.equal(c.VTyp(1))
  c.eval(env, app(var(1), typ(1)))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
  c.eval([], app(ctr("A", []), typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(c.VCtr("A", []), s)))
  c.eval([], app(rcd([]), typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(c.VRcd([]), s)))
  let env = [c.VNeut(c.HVar(0), [])]
  c.eval(env, app(dot(var(0), "a"), typ(1)))
  |> should.equal(c.VNeut(c.HVar(0), [c.EDot("a"), c.EApp(c.VTyp(1))]))
  let env = [c.VLam("a", [], var(0))]
  c.eval(env, app(ann(var(0), typ(1)), typ(1)))
  |> should.equal(c.VTyp(1))
  c.eval([], app(lam("a", var(0)), typ(1)))
  |> should.equal(c.VTyp(1))
  c.eval([], app(pi("a", typ(0), typ(1)), typ(1)))
  |> should.equal(c.VErr(c.NotAFunction(c.VPi("a", [], c.VTyp(0), typ(1)), s)))
  c.eval([], app(app(lambda(["a", "b"], var(0)), typ(2)), typ(1)))
  |> should.equal(c.VTyp(1))
  c.eval([], app(app(lambda(["a", "b"], var(1)), typ(2)), typ(1)))
  |> should.equal(c.VTyp(2))
  c.eval([], app(match(typ(0), [case_(c.PAny, lam("a", var(0)))]), typ(1)))
  |> should.equal(c.VTyp(1))
  c.eval([], app(bad(lam("a", var(0)), []), typ(1)))
  |> should.equal(c.VBad(c.VTyp(1), []))
  c.eval([], app(err(c.TODO("", s)), typ(1)))
  |> should.equal(c.VErr(c.TODO("", s)))
}

pub fn app_infer_test() {
  let ty = c.VPi("x", [], v32t, i32t)
  let ctx = [#("f", ty)]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(ty)
  c.infer(0, ctx, [], [], app(var(0), i32(1))) |> should.equal(v32t)
  c.infer(0, ctx, [], [], app(var(0), i64(1)))
  |> should.equal(c.VBad(v32t, [c.TypeMismatch(v64t, v32t, s)]))

  let ty = c.VPi("x", [], v32t, i64t)
  let ctx = [#("f", ty)]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(ty)
  c.infer(0, ctx, [], [], app(var(0), i32(1))) |> should.equal(v64t)
}

pub fn app_check_test() {
  let ty = c.VPi("x", [], v32t, i32t)
  let ctx = [#("f", ty)]
  c.check(0, ctx, [], [], app(var(0), i32(1)), v32t)
  |> should.equal(v32t)
  c.check(0, ctx, [], [], app(var(0), i32(1)), v64t)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s)))

  let ty = c.VPi("x", [], v32t, i64t)
  let ctx = [#("f", ty)]
  c.check(0, ctx, [], [], app(var(0), i32(1)), v64t)
  |> should.equal(v64t)
  c.check(0, ctx, [], [], app(var(0), i32(1)), v32t)
  |> should.equal(c.VErr(c.TypeMismatch(v64t, v32t, s)))
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

pub fn match_infer_test() {
  let cat_ty = typ(0)
  let tenv = [
    #("A", c.CtrDef([], [], cat_ty)),
    #("B", c.CtrDef([], [], cat_ty)),
    #("C", c.CtrDef([], [], cat_ty)),
  ]

  // Pattern match assigning "kibble portions" based on the cat
  let match_expr =
    match(ann(ctr("C", []), cat_ty), [
      c.Case(c.PCtr("A", []), lit(c.I32(1)), s),
      c.Case(c.PCtr("B", []), lit(c.I32(2)), s),
      c.Case(c.PCtr("C", []), lit(c.I32(100)), s),
      // Accommodating the insatiable hunger!
    ])

  c.infer(0, [], [], tenv, match_expr)
  |> should.equal(c.VLitT(c.I32T))
}

pub fn match_check_test() {
  let cat_ty = typ(0)
  let tenv = [
    #("A", c.CtrDef([], [], cat_ty)),
    #("B", c.CtrDef([], [], cat_ty)),
    #("C", c.CtrDef([], [], cat_ty)),
  ]

  let match_expr =
    match(ann(ctr("C", []), cat_ty), [
      c.Case(c.PCtr("A", []), lit(c.I32(1)), s),
      c.Case(c.PCtr("B", []), lit(c.I32(2)), s),
      c.Case(c.PCtr("C", []), lit(c.I32(100)), s),
    ])

  // Valid bidirectional check
  c.check(0, [], [], tenv, match_expr, c.VLitT(c.I32T))
  |> should.equal(c.VLitT(c.I32T))

  // Checking mismatch (Expecting a Float when we returned an Int)
  c.check(0, [], [], tenv, match_expr, c.VLitT(c.F32T))
  |> should.equal(c.VErr(c.TypeMismatch(c.VLitT(c.I32T), c.VLitT(c.F32T), s)))
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

fn litt(t) {
  c.Term(c.LitT(t), s)
}

fn i32(v) {
  lit(c.I32(v))
}

fn i64(v) {
  lit(c.I64(v))
}

fn v32(v) {
  c.VLit(c.I32(v))
}

fn v64(v) {
  c.VLit(c.I64(v))
}

const i32t = c.Term(c.LitT(c.I32T), s)

const v32t = c.VLitT(c.I32T)

const i64t = c.Term(c.LitT(c.I64T), s)

const v64t = c.VLitT(c.I64T)

fn var(i) {
  c.Term(c.Var(i), s)
}

fn ctr(k, args) {
  c.Term(c.Ctr(k, args), s)
}

fn rcd(fields) {
  c.Term(c.Rcd(fields), s)
}

fn dot(arg, name) {
  c.Term(c.Dot(arg, name), s)
}

fn pi(name, in, out) {
  c.Term(c.Pi(name, in, out), s)
}

fn lam(name, body) {
  c.Term(c.Lam(name, body), s)
}

fn lambda(xs, body) -> c.Term {
  case xs {
    [] -> body
    [x, ..xs] -> c.Term(c.Lam(x, lambda(xs, body)), s)
  }
}

fn ann(x, t) {
  c.Term(c.Ann(x, t), s)
}

fn app(f, a) {
  c.Term(c.App(f, a), s)
}

fn apply(fun, args) -> c.Term {
  case args {
    [] -> fun
    [arg, ..args] -> apply(c.Term(c.App(fun, arg), s), args)
  }
}

fn match(arg, cases) {
  c.Term(c.Match(arg, cases), s)
}

fn bad(term, errors) {
  c.Term(c.Bad(term, errors), s)
}

fn err(e) {
  c.Term(c.Err(e), s)
}

fn case_(p, b) {
  c.Case(p, b, s)
}
