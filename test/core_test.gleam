import core as c
import gleam/option.{None, Some}
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
  c.check(0, [], [], [], typ(0), c.VTyp(1), s2) |> should.equal(c.VTyp(1))

  c.check(0, [], [], [], typ(1), c.VTyp(0), s2)
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(0), s, s2)))
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
  c.check(0, [], [], [], lit(c.I32(1)), c.VLitT(c.I32T), s2)
  |> should.equal(c.VLitT(c.I32T))
  c.check(0, [], [], [], lit(c.I64(1)), c.VLitT(c.I64T), s2)
  |> should.equal(c.VLitT(c.I64T))
  c.check(0, [], [], [], lit(c.U32(1)), c.VLitT(c.U32T), s2)
  |> should.equal(c.VLitT(c.U32T))
  c.check(0, [], [], [], lit(c.U64(1)), c.VLitT(c.U64T), s2)
  |> should.equal(c.VLitT(c.U64T))
  c.check(0, [], [], [], lit(c.F32(1.0)), c.VLitT(c.F32T), s2)
  |> should.equal(c.VLitT(c.F32T))
  c.check(0, [], [], [], lit(c.F64(1.0)), c.VLitT(c.F64T), s2)
  |> should.equal(c.VLitT(c.F64T))

  c.check(0, [], [], [], lit(c.I32(1)), c.VLitT(c.I64T), s2)
  |> should.equal(
    c.VErr(c.TypeMismatch(c.VLitT(c.I32T), c.VLitT(c.I64T), s, s2)),
  )
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
  c.check(0, [], [], [], litt(c.I32T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.I64T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.U32T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.U64T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.F32T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))
  c.check(0, [], [], [], litt(c.F64T), c.VTyp(0), s2) |> should.equal(c.VTyp(0))

  c.check(0, [], [], [], litt(c.I32T), c.VTyp(1), s2)
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s, s2)))
}

// --- Var --- \\
pub fn var_eval_test() {
  let env = [v32(0)]
  c.eval(env, var(0)) |> should.equal(v32(0))
  c.eval(env, var(1)) |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_unify_test() {
  c.unify(0, [], v32t, hole(1), s, s2) |> should.equal(Ok([#(1, v32t)]))
  c.unify(0, [], hole(1), v32t, s, s2) |> should.equal(Ok([#(1, v32t)]))
  c.unify(0, [#(0, v64t)], hole(1), v32t, s, s2)
  |> should.equal(Ok([#(1, v32t), #(0, v64t)]))
}

pub fn var_infer_test() {
  let ctx = [#("x", v32t)]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(v32t)
  c.infer(0, ctx, [], [], var(1))
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
}

pub fn var_check_test() {
  let ctx = [#("x", v32t)]
  c.check(0, ctx, [], [], var(0), v32t, s2) |> should.equal(v32t)

  c.check(0, ctx, [], [], var(1), v32t, s2)
  |> should.equal(c.VErr(c.VarUndefined(1, s)))
  c.check(0, ctx, [], [], var(0), v64t, s2)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s, s2)))
}

// --- Ctr --- \\
pub fn ctr_eval_test() {
  c.eval([], ctr("A", [])) |> should.equal(c.VCtr("A", []))
  c.eval([], ctr("A", [#("x", i32(0))]))
  |> should.equal(c.VCtr("A", [#("x", v32(0))]))
  c.eval([], ctr("A", [#("x", i32(0)), #("y", i32(1))]))
  |> should.equal(c.VCtr("A", [#("x", v32(0)), #("y", v32(1))]))
}

pub fn ctr_unify_tag_test() {
  c.unify(0, [], c.VCtr("", []), c.VCtr("", []), s, s2) |> should.equal(Ok([]))
  c.unify(0, [], c.VCtr("", []), c.VCtr("A", []), s, s2)
  |> should.equal(Error(c.TypeMismatch(c.VCtr("", []), c.VCtr("A", []), s, s2)))
  c.unify(0, [], c.VCtr("A", []), c.VCtr("A", []), s, s2)
  |> should.equal(Ok([]))
}

pub fn ctr_unify_args_missing_test() {
  let ab = c.VCtr("", [#("a", v32t), #("b", v64t)])
  c.unify(0, [], ab, c.VCtr("", []), s, s2)
  |> should.equal(Error(c.CtrMissingArgs(["a", "b"], s2)))
  c.unify(0, [], c.VCtr("", []), ab, s, s2)
  |> should.equal(Error(c.CtrMissingArgs(["a", "b"], s)))
}

pub fn ctr_unify_args_mismatch_test() {
  c.unify(0, [], c.VCtr("", [#("a", v32t)]), c.VCtr("", [#("a", v64t)]), s, s2)
  |> should.equal(Error(c.TypeMismatch(v32t, v64t, s, s2)))
}

pub fn ctr_unify_args_order_test() {
  let ab = c.VCtr("", [#("a", v32t), #("b", v64t)])
  let ba = c.VCtr("", [#("b", v64t), #("a", v32t)])
  c.unify(0, [], ab, ab, s, s2) |> should.equal(Ok([]))
  c.unify(0, [], ab, ba, s, s2) |> should.equal(Ok([]))
}

pub fn ctr_unify_args_bind_test() {
  let a = c.VCtr("", [#("a", v32t)])
  let b = c.VCtr("", [#("a", hole(1))])
  c.unify(0, [], a, b, s, s2) |> should.equal(Ok([#(1, v32t)]))
}

pub fn instantiate_ctr_ret_test() {
  let ctr_def = c.CtrDef([], [], i32t)
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(#([], [], v32t, []))
}

pub fn instantiate_ctr_ret_bind_test() {
  let ctr_def = c.CtrDef(["a"], [], var(0))
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(#([v32t], [], v32t, []))
}

pub fn instantiate_ctr_ret_mismatch_test() {
  let ctr_def = c.CtrDef([], [], i32t)
  c.instantiate_ctr(0, [], "A", ctr_def, v64t, s2)
  |> should.equal(#([], [], v32t, [c.TypeMismatch(v32t, v64t, s, s2)]))
}

pub fn instantiate_ctr_args_test() {
  let ctr_def = c.CtrDef([], [#("x", i64t, None)], i32t)
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(#([], [#("x", #(v64t, None))], v32t, []))
}

pub fn instantiate_ctr_args_bind_test() {
  let ctr_def = c.CtrDef(["a"], [#("x", var(0), None)], var(0))
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(#([v32t], [#("x", #(v32t, None))], v32t, []))
}

pub fn instantiate_ctr_args_undefined_test() {
  let ctr_def = c.CtrDef([], [#("x", var(0), None)], i32t)
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(
    #([], [#("x", #(c.VErr(c.VarUndefined(0, s)), None))], v32t, []),
  )
}

pub fn instantiate_ctr_args_unsolved_test() {
  let ctr_def = c.CtrDef(["a"], [#("x", var(0), None)], i32t)
  c.instantiate_ctr(0, [], "A", ctr_def, v32t, s2)
  |> should.equal(
    #(
      [c.VNeut(c.HMeta(0), [])],
      [#("x", #(c.VNeut(c.HMeta(0), []), None))],
      v32t,
      [
        c.CtrUnsolvedParam("A", ctr_def, 0, s2),
      ],
    ),
  )
}

pub fn instantiate_ctr_args_multiple_test() {
  let ctr_def =
    c.CtrDef(
      ["a", "b"],
      [#("x", var(0), None), #("y", var(1), None)],
      ctr("T", [#("z", var(0)), #("w", var(1))]),
    )
  let ret_ty = c.VCtr("T", [#("z", v32t), #("w", v64t)])
  c.instantiate_ctr(0, [], "A", ctr_def, ret_ty, s2)
  |> should.equal(
    #([v32t, v64t], [#("x", #(v32t, None)), #("y", #(v64t, None))], ret_ty, []),
  )
}

pub fn ctr_infer_test() {
  c.infer(0, [], [], [], ctr("A", []))
  // |> should.equal(c.VErr(c.TypeAnnotationNeeded(ctr("A", []))))
  |> should.equal(c.VErr(c.CtrUndefined("A", s)))
}

pub fn ctr_check_undefined_test() {
  let tenv = []
  c.check(0, [], [], tenv, ctr("A", []), v32t, s2)
  |> should.equal(c.VErr(c.CtrUndefined("A", s2)))
}

pub fn ctr_check_ret_test() {
  let tenv = [#("A", c.CtrDef([], [], i32t))]
  c.check(0, [], [], tenv, ctr("A", []), v32t, s2)
  |> should.equal(v32t)
}

pub fn ctr_check_ret_mismatch_test() {
  let tenv = [#("A", c.CtrDef([], [], i32t))]
  c.check(0, [], [], tenv, ctr("A", []), v64t, s2)
  |> should.equal(c.VBad(v32t, [c.TypeMismatch(v32t, v64t, s, s2)]))
}

pub fn ctr_check_params_undefined_test() {
  let tenv = [#("A", c.CtrDef([], [#("x", var(0), None)], i32t))]
  c.check(0, [], [], tenv, ctr("A", [#("x", i32(1))]), v32t, s2)
  |> should.equal(c.VBad(v32t, [c.VarUndefined(0, s)]))
}

pub fn ctr_check_args_test() {
  let tenv = [#("A", c.CtrDef(["a"], [#("x", var(0), None)], var(0)))]
  c.check(0, [], [], tenv, ctr("A", [#("x", i32(1))]), v32t, s2)
  |> should.equal(v32t)
}

pub fn ctr_check_args_too_many_test() {
  let ctr_def = c.CtrDef([], [], i32t)
  let tenv = [#("A", ctr_def)]
  c.check(0, [], [], tenv, ctr("A", [#("x", i32(1))]), v32t, s2)
  |> should.equal(c.VBad(v32t, [c.CtrTooManyArgs("A", 1, ctr_def, s2)]))
}

pub fn ctr_check_args_too_few_test() {
  let ctr_def = c.CtrDef([], [#("x", i64t, None)], i32t)
  let tenv = [#("A", ctr_def)]
  c.check(0, [], [], tenv, ctr("A", []), v32t, s2)
  |> should.equal(c.VBad(v32t, [c.CtrTooFewArgs("A", 0, ctr_def, s2)]))
}

pub fn ctr_check_args_unsolved_test() {
  let ctr_def =
    c.CtrDef(["a", "b"], [#("x", var(0), None), #("y", var(1), None)], var(0))
  let tenv = [#("A", ctr_def)]
  c.check(0, [], [], tenv, ctr("A", [#("x", i32(1)), #("y", i64(2))]), v32t, s2)
  |> should.equal(c.VBad(v32t, [c.CtrUnsolvedParam("A", ctr_def, 1, s2)]))

  let ctr_def =
    c.CtrDef(["a", "b"], [#("x", var(0), None), #("y", var(1), None)], var(1))
  let tenv = [#("A", ctr_def)]
  c.check(0, [], [], tenv, ctr("A", [#("x", i32(1)), #("y", i64(2))]), v64t, s2)
  |> should.equal(c.VBad(v64t, [c.CtrUnsolvedParam("A", ctr_def, 0, s2)]))
}

pub fn ctr_check_args_multiple_test() {
  let ctr_def =
    c.CtrDef(
      ["a", "b"],
      [#("x", var(0), None), #("y", var(1), None)],
      ctr("T", [#("z", var(0)), #("w", var(1))]),
    )
  let tenv = [#("A", ctr_def)]
  let term = ctr("A", [#("x", i32(1)), #("y", i64(2))])
  let ty = c.VCtr("T", [#("z", v32t), #("w", v64t)])
  c.check(0, [], [], tenv, term, ty, s2) |> should.equal(ty)
}

// --- Dot --- \\
pub fn dot_eval_test() {
  c.eval([], dot(i32(1), "a"))
  |> should.equal(c.VErr(c.DotOnNonCtr(v32(1), "a", s)))
  c.eval([], dot(ctr("", []), "a"))
  |> should.equal(c.VErr(c.DotArgNotFound("a", [], s)))
  c.eval([], dot(ctr("", [#("a", i32(1)), #("b", i64(2))]), "a"))
  |> should.equal(v32(1))
  c.eval([], dot(ctr("", [#("a", i32(1)), #("b", i64(2))]), "b"))
  |> should.equal(v64(2))
  c.eval([c.VNeut(c.HVar(0), [])], dot(var(0), "a"))
  |> should.equal(c.VNeut(c.HVar(0), [c.EDot("a")]))
}

pub fn dot_infer_non_ctr_test() {
  c.infer(0, [], [], [], dot(i32(1), "x"))
  |> should.equal(c.VErr(c.DotOnNonCtr(v32t, "x", s)))
}

pub fn dot_infer_record_test() {
  c.infer(0, [], [], [], dot(ctr("", [#("x", i32(1)), #("y", i64(2))]), "x"))
  |> should.equal(v32t)

  c.infer(0, [], [], [], dot(ctr("", [#("x", i32(1)), #("y", i64(2))]), "y"))
  |> should.equal(v64t)
}

pub fn dot_infer_record_not_found_test() {
  c.infer(0, [], [], [], dot(ctr("", []), "x"))
  |> should.equal(c.VErr(c.DotArgNotFound("x", [], s)))
}

pub fn dot_infer_ctr_test() {
  let tenv = [#("A", c.CtrDef([], [#("x", i32t, None)], i64t))]
  c.infer(0, [], [], tenv, dot(ctr("A", []), "x"))
  |> should.equal(v32t)
}

pub fn dot_check_test() {
  let record = ctr("", [#("a", i32(1)), #("b", i64(2))])
  c.check(0, [], [], [], dot(record, "a"), v32t, s2)
  |> should.equal(v32t)
  c.check(0, [], [], [], dot(record, "b"), v64t, s2)
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

  c.infer(0, [], [], [], ann(i32t, i32_2(1)))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), v32(1), s, s2)))

  c.infer(0, [], [], [], ann(typ(0), typ(1)))
  |> should.equal(c.VTyp(1))

  c.infer(0, [], [], [], ann(typ(1), c.Term(c.Typ(0), s2)))
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(2), c.VTyp(0), s, s2)))
}

pub fn ann_check_test() {
  c.check(0, [], [], [], ann(i32(1), i32t), v32t, s2)
  |> should.equal(v32t)

  c.check(0, [], [], [], ann(i32(1), i32t), v64t, s2)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s, s2)))
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
  c.check(0, [], [], [], lam("x", var(0)), ty, s2)
  |> should.equal(ty)

  c.check(0, [], [], [], lam("y", var(0)), c.VTyp(0), s2)
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
  c.infer(0, [], [], [], pi("y", var(1), var(2)))
  |> should.equal(
    c.VBad(c.VTyp(0), [c.VarUndefined(1, s), c.VarUndefined(2, s)]),
  )
}

pub fn pi_check_test() {
  let term = pi("x", typ(0), typ(1))
  c.check(0, [], [], [], term, c.VTyp(0), s2)
  |> should.equal(c.VTyp(0))

  c.check(0, [], [], [], term, c.VTyp(1), s2)
  |> should.equal(c.VErr(c.TypeMismatch(c.VTyp(0), c.VTyp(1), s, s2)))
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
  c.infer(0, ctx, [], [], app(var(0), i64_2(1)))
  |> should.equal(c.VBad(v32t, [c.TypeMismatch(v64t, v32t, s2, s2)]))

  let ty = c.VPi("x", [], v32t, i64t)
  let ctx = [#("f", ty)]
  c.infer(0, ctx, [], [], var(0)) |> should.equal(ty)
  c.infer(0, ctx, [], [], app(var(0), i32(1))) |> should.equal(v64t)
}

pub fn app_check_test() {
  let ty = c.VPi("x", [], v32t, i32t)
  let ctx = [#("f", ty)]
  c.check(0, ctx, [], [], app(var(0), i32(1)), v32t, s2)
  |> should.equal(v32t)
  c.check(0, ctx, [], [], app(var(0), i32(1)), v64t, s2)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s, s2)))

  let ty = c.VPi("x", [], v32t, i64t)
  let ctx = [#("f", ty)]
  c.check(0, ctx, [], [], app(var(0), i32(1)), v64t, s2)
  |> should.equal(v64t)
  c.check(0, ctx, [], [], app(var(0), i32(1)), v32t, s2)
  |> should.equal(c.VErr(c.TypeMismatch(v64t, v32t, s, s2)))
}

// --- Match --- \\
pub fn match_pattern_any_test() {
  c.match_pattern(c.PAny, v32(1)) |> should.equal(Ok([]))
}

pub fn match_pattern_as_test() {
  c.match_pattern(pvar("a"), v32(1)) |> should.equal(Ok([v32(1)]))
}

pub fn match_pattern_typ_test() {
  c.match_pattern(c.PTyp(0), c.VTyp(0)) |> should.equal(Ok([]))
  c.match_pattern(c.PTyp(0), c.VTyp(1)) |> should.equal(Error(Nil))
}

pub fn match_pattern_lit_test() {
  c.match_pattern(c.PLit(c.I32(1)), v32(1)) |> should.equal(Ok([]))
  c.match_pattern(c.PLit(c.I32(1)), v32(2)) |> should.equal(Error(Nil))
}

pub fn match_pattern_ctr_tag_test() {
  c.match_pattern(c.PCtr("A", []), c.VCtr("A", [])) |> should.equal(Ok([]))
  c.match_pattern(c.PCtr("A", []), c.VCtr("B", [])) |> should.equal(Error(Nil))
}

pub fn match_pattern_ctr_args_missing_test() {
  c.match_pattern(c.PCtr("A", [#("x", c.PAny)]), c.VCtr("A", []))
  |> should.equal(Error(Nil))
}

pub fn match_pattern_ctr_args_unused_test() {
  c.match_pattern(c.PCtr("A", []), c.VCtr("A", [#("x", v32(1))]))
  |> should.equal(Ok([]))
}

pub fn match_pattern_ctr_args_test() {
  c.match_pattern(
    c.PCtr("A", [#("x", pvar("a"))]),
    c.VCtr("A", [#("x", v32(1))]),
  )
  |> should.equal(Ok([v32(1)]))

  c.match_pattern(
    c.PCtr("A", [#("x", pvar("a")), #("y", pvar("b"))]),
    c.VCtr("A", [#("x", v32(1)), #("y", v64(2))]),
  )
  |> should.equal(Ok([v32(1), v64(2)]))
}

pub fn match_pattern_bad_test() {
  c.match_pattern(c.PTyp(0), c.VBad(c.VTyp(0), [])) |> should.equal(Ok([]))
}

pub fn match_eval_test() {
  c.eval([], match(i32(1), [case_(c.PAny, i64(2))]))
  |> should.equal(v64(2))

  let env = [c.VNeut(c.HVar(0), [])]
  let cases = [case_(c.PAny, i32(1))]
  c.eval(env, match(var(0), cases))
  |> should.equal(c.VNeut(c.HVar(0), [c.EMatch(env, cases)]))
}

pub fn bind_pattern_any_test() {
  c.bind_pattern(0, [], [], [], c.PAny, v32t, s, s2)
  |> should.equal(#(0, [], []))
  c.bind_pattern(0, [], [], [], pvar("a"), v32t, s, s2)
  |> should.equal(#(1, [#("a", v32t)], []))
}

pub fn bind_pattern_as_test() {
  c.bind_pattern(0, [], [], [], pvar("x"), v32t, s, s2)
  |> should.equal(#(1, [#("x", v32t)], []))
}

pub fn bind_pattern_typ_test() {
  c.bind_pattern(0, [], [], [], c.PTyp(0), c.VTyp(0), s, s2)
  |> should.equal(#(0, [], [c.TypeMismatch(c.VTyp(1), c.VTyp(0), s, s2)]))
  c.bind_pattern(0, [], [], [], c.PTyp(0), c.VTyp(1), s, s2)
  |> should.equal(#(0, [], []))
}

pub fn bind_pattern_lit_test() {
  c.bind_pattern(0, [], [], [], c.PLit(c.I32(1)), c.VTyp(0), s, s2)
  |> should.equal(#(0, [], [c.TypeMismatch(v32t, c.VTyp(0), s, s2)]))
  c.bind_pattern(0, [], [], [], c.PLit(c.I32(1)), v32t, s, s2)
  |> should.equal(#(0, [], []))
}

pub fn bind_pattern_ctr_pattern_mismatch_test() {
  c.bind_pattern(0, [], [], [], c.PCtr("", []), v32t, s, s2)
  |> should.equal(#(0, [], [c.PatternMismatch(c.PCtr("", []), v32t, s, s2)]))
}

pub fn bind_pattern_ctr_record_empty_test() {
  c.bind_pattern(0, [], [], [], c.PCtr("", []), c.VCtr("", []), s, s2)
  |> should.equal(#(0, [], []))
}

pub fn bind_pattern_ctr_record_unused_test() {
  let p = c.PCtr("", [])
  let t = c.VCtr("", [#("a", v32t)])
  c.bind_pattern(0, [], [], [], p, t, s, s2)
  |> should.equal(#(0, [], []))
}

pub fn bind_pattern_ctr_record_missing_test() {
  let p = c.PCtr("", [#("a", pvar("x")), #("b", pvar("y"))])
  let t = c.VCtr("", [])
  c.bind_pattern(0, [], [], [], p, t, s, s2)
  |> should.equal(
    #(2, [#("y", hole(1)), #("x", hole(0))], [c.CtrMissingArgs(["a", "b"], s2)]),
  )
}

pub fn bind_pattern_ctr_test() {
  c.bind_pattern(0, [], [], [], c.PCtr("A", []), v32t, s, s2)
  |> should.equal(#(0, [], [c.CtrUndefined("A", s)]))
  // let tenv = [#("A", c.CtrDef([], [], i32t))]
  // c.bind_pattern(0, [], [], tenv, c.PCtr("A", []), v32t, s, s2)
  // |> should.equal(#(0, [], []))

  // let ctr_def = c.CtrDef([], [], i32t)
  // let tenv = [#("A", ctr_def)]
  // c.bind_pattern(0, [], [], tenv, c.PCtr("A", [#("x", pvar("a"))]), v32t, s, s2)
  // |> should.equal(#(0, [], [c.CtrTooManyArgs("A", 1, ctr_def, s)]))

  // let ctr_def = c.CtrDef([], [#("x", i64t, None)], i32t)
  // let tenv = [#("A", ctr_def)]
  // c.bind_pattern(0, [], [], tenv, c.PCtr("A", []), v32t, s, s2)
  // |> should.equal(#(0, [], [c.CtrTooFewArgs("A", 0, ctr_def, s)]))

  // let ctr_def = c.CtrDef(["a"], [#("x", var(0), None)], var(0))
  // let tenv = [#("A", ctr_def)]
  // c.bind_pattern(0, [], [], tenv, c.PCtr("A", [#("x", pvar("y"))]), v32t, s, s2)
  // |> should.equal(#(1, [#("y", v32t)], []))

  // let ctr_def =
  //   c.CtrDef(["a", "b"], [#("x", var(0), None), #("y", var(1), None)], var(0))
  // let tenv = [#("A", ctr_def)]
  // let ret_ty = c.PCtr("A", [#("x", pvar("x")), #("y", pvar("y"))])
  // c.bind_pattern(0, [], [], tenv, ret_ty, v32t, s, s2)
  // |> should.equal(
  //   #(2, [#("y", c.VNeut(c.HMeta(1), [])), #("x", v32t)], [
  //     c.CtrUnsolvedParam("A", ctr_def, 1, s),
  //   ]),
  // )

  // let ctr_def =
  //   c.CtrDef(["a", "b"], [#("x", var(0), None), #("y", var(1), None)], var(1))
  // let tenv = [#("A", ctr_def)]
  // let ret_ty = c.PCtr("A", [#("x", pvar("x")), #("y", pvar("y"))])
  // c.bind_pattern(0, [], [], tenv, ret_ty, v32t, s, s2)
  // |> should.equal(
  //   #(2, [#("y", v32t), #("x", c.VNeut(c.HMeta(0), []))], [
  //     c.CtrUnsolvedParam("A", ctr_def, 0, s),
  //   ]),
  // )
}

pub fn match_infer_test() {
  c.infer(0, [], [], [], match(i32(1), []))
  |> should.equal(c.VErr(c.MatchEmpty(v32t, s)))

  c.infer(0, [], [], [], match(i32(1), [case_(c.PAny, i64(2))]))
  |> should.equal(v64t)

  let term = match(i32(1), [case_(c.PAny, i64_2(2)), case_(c.PAny, typ(0))])
  c.infer(0, [], [], [], term)
  |> should.equal(c.VBad(v64t, [c.TypeMismatch(c.VTyp(1), v64t, s, s2)]))

  c.infer(0, [], [], [], match(i32(1), [case_(pvar("a"), var(0))]))
  |> should.equal(v32t)
}

pub fn match_check_test() {
  c.check(0, [], [], [], match(i32(1), []), v64t, s2)
  |> should.equal(c.VErr(c.MatchEmpty(v32t, s)))

  c.check(0, [], [], [], match(i32(1), [case_(c.PAny, i64(2))]), v64t, s2)
  |> should.equal(v64t)

  let term = match(i32(1), [case_(c.PAny, i64(2))])
  c.check(0, [], [], [], term, c.VTyp(0), s2)
  |> should.equal(c.VErr(c.TypeMismatch(v64t, c.VTyp(0), s, s2)))

  let term = match(i32(1), [case_(c.PAny, i64_2(2)), case_(c.PAny, typ(0))])
  c.check(0, [], [], [], term, v64t, s2)
  |> should.equal(c.VBad(v64t, [c.TypeMismatch(c.VTyp(1), v64t, s, s2)]))

  let term = match(i32(1), [case_(c.PAny, i64(2)), case_(c.PAny, typ(0))])
  c.check(0, [], [], [], term, c.VTyp(2), s2)
  |> should.equal(c.VErr(c.TypeMismatch(v64t, c.VTyp(2), s, s2)))

  c.check(0, [], [], [], match(i32(1), [case_(pvar("a"), var(0))]), v32t, s2)
  |> should.equal(v32t)

  c.check(0, [], [], [], match(i32(1), [case_(pvar("a"), var(0))]), v64t, s2)
  |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s, s2)))
}

// --- Bad --- \\
// TODO

// --- Err --- \\
// TODO

// --- HELPERS to make writing ASTs less painful ---
const s = c.Span("core_test", 1, 1)

const s2 = c.Span("core_test", 2, 2)

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

fn i32_2(v) {
  c.Term(c.Lit(c.I32(v)), s2)
}

fn i64(v) {
  lit(c.I64(v))
}

fn i64_2(v) {
  c.Term(c.Lit(c.I64(v)), s2)
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

fn pvar(x) {
  c.PAs(c.PAny, x)
}

fn hole(i) {
  c.VNeut(c.HMeta(i), [])
}
