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
pub fn eval_typ_test() {
  c.eval([], typ(0, s1)) |> should.equal(c.VTyp(0))
  c.eval([], typ(1, s1)) |> should.equal(c.VTyp(1))
}

pub fn infer_typ_test() {
  c.infer(0, [], [], [], typ(0, s1))
  |> should.equal(#(c.VTyp(0), c.VTyp(1), [], []))
}

pub fn check_typ_test() {
  c.check(0, [], [], [], typ(0, s1), c.VTyp(1), s2)
  |> should.equal(#(c.VTyp(0), [], []))

  c.check(0, [], [], [], typ(1, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(c.VTyp(2), c.VTyp(0), s1, s2)]))
}

// --- Lit --- \\
pub fn eval_lit_test() {
  c.eval([], lit(c.I32(1), s1)) |> should.equal(c.VLit(c.I32(1)))
  c.eval([], lit(c.I64(1), s1)) |> should.equal(c.VLit(c.I64(1)))
  c.eval([], lit(c.U32(1), s1)) |> should.equal(c.VLit(c.U32(1)))
  c.eval([], lit(c.U64(1), s1)) |> should.equal(c.VLit(c.U64(1)))
  c.eval([], lit(c.F32(1.0), s1)) |> should.equal(c.VLit(c.F32(1.0)))
  c.eval([], lit(c.F64(1.0), s1)) |> should.equal(c.VLit(c.F64(1.0)))
}

pub fn infer_lit_test() {
  c.infer(0, [], [], [], lit(c.I32(1), s1))
  |> should.equal(#(c.VLit(c.I32(1)), c.VLitT(c.I32T), [], []))
  c.infer(0, [], [], [], lit(c.I64(1), s1))
  |> should.equal(#(c.VLit(c.I64(1)), c.VLitT(c.I64T), [], []))
  c.infer(0, [], [], [], lit(c.U32(1), s1))
  |> should.equal(#(c.VLit(c.U32(1)), c.VLitT(c.U32T), [], []))
  c.infer(0, [], [], [], lit(c.U64(1), s1))
  |> should.equal(#(c.VLit(c.U64(1)), c.VLitT(c.U64T), [], []))
  c.infer(0, [], [], [], lit(c.F32(1.0), s1))
  |> should.equal(#(c.VLit(c.F32(1.0)), c.VLitT(c.F32T), [], []))
  c.infer(0, [], [], [], lit(c.F64(1.0), s1))
  |> should.equal(#(c.VLit(c.F64(1.0)), c.VLitT(c.F64T), [], []))
}

pub fn check_lit_test() {
  c.check(0, [], [], [], lit(c.I32(1), s1), c.VLitT(c.I32T), s2)
  |> should.equal(#(c.VLit(c.I32(1)), [], []))
  c.check(0, [], [], [], lit(c.I64(1), s1), c.VLitT(c.I64T), s2)
  |> should.equal(#(c.VLit(c.I64(1)), [], []))
  c.check(0, [], [], [], lit(c.U32(1), s1), c.VLitT(c.U32T), s2)
  |> should.equal(#(c.VLit(c.U32(1)), [], []))
  c.check(0, [], [], [], lit(c.U64(1), s1), c.VLitT(c.U64T), s2)
  |> should.equal(#(c.VLit(c.U64(1)), [], []))
  c.check(0, [], [], [], lit(c.F32(1.0), s1), c.VLitT(c.F32T), s2)
  |> should.equal(#(c.VLit(c.F32(1.0)), [], []))
  c.check(0, [], [], [], lit(c.F64(1.0), s1), c.VLitT(c.F64T), s2)
  |> should.equal(#(c.VLit(c.F64(1.0)), [], []))

  c.check(0, [], [], [], lit(c.I32(1), s1), c.VLitT(c.I64T), s2)
  |> should.equal(
    #(c.VErr, [], [c.TypeMismatch(c.VLitT(c.I32T), c.VLitT(c.I64T), s1, s2)]),
  )
}

// --- LitT --- \\
pub fn eval_litt_test() {
  c.eval([], litt(c.I32T, s1)) |> should.equal(c.VLitT(c.I32T))
  c.eval([], litt(c.I64T, s1)) |> should.equal(c.VLitT(c.I64T))
  c.eval([], litt(c.U32T, s1)) |> should.equal(c.VLitT(c.U32T))
  c.eval([], litt(c.U64T, s1)) |> should.equal(c.VLitT(c.U64T))
  c.eval([], litt(c.F32T, s1)) |> should.equal(c.VLitT(c.F32T))
  c.eval([], litt(c.F64T, s1)) |> should.equal(c.VLitT(c.F64T))
}

pub fn infer_litt_test() {
  c.infer(0, [], [], [], litt(c.I32T, s1))
  |> should.equal(#(c.VLitT(c.I32T), c.VTyp(0), [], []))
  c.infer(0, [], [], [], litt(c.I64T, s1))
  |> should.equal(#(c.VLitT(c.I64T), c.VTyp(0), [], []))
  c.infer(0, [], [], [], litt(c.U32T, s1))
  |> should.equal(#(c.VLitT(c.U32T), c.VTyp(0), [], []))
  c.infer(0, [], [], [], litt(c.U64T, s1))
  |> should.equal(#(c.VLitT(c.U64T), c.VTyp(0), [], []))
  c.infer(0, [], [], [], litt(c.F32T, s1))
  |> should.equal(#(c.VLitT(c.F32T), c.VTyp(0), [], []))
  c.infer(0, [], [], [], litt(c.F64T, s1))
  |> should.equal(#(c.VLitT(c.F64T), c.VTyp(0), [], []))
}

pub fn check_litt_test() {
  c.check(0, [], [], [], litt(c.I32T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.I32T), [], []))
  c.check(0, [], [], [], litt(c.I64T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.I64T), [], []))
  c.check(0, [], [], [], litt(c.U32T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.U32T), [], []))
  c.check(0, [], [], [], litt(c.U64T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.U64T), [], []))
  c.check(0, [], [], [], litt(c.F32T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.F32T), [], []))
  c.check(0, [], [], [], litt(c.F64T, s1), c.VTyp(0), s2)
  |> should.equal(#(c.VLitT(c.F64T), [], []))

  c.check(0, [], [], [], litt(c.I32T, s1), c.VTyp(1), s2)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(c.VTyp(0), c.VTyp(1), s1, s2)]))
}

// --- Var --- \\
pub fn eval_var_test() {
  let env = [v32(0)]
  c.eval(env, var(0, s1)) |> should.equal(v32(0))
  c.eval(env, var(1, s1)) |> should.equal(c.VErr)
}

pub fn unify_var_test() {
  c.unify(0, [], v32t, vhole(1), s1, s2) |> should.equal(Ok([#(1, v32t)]))
  c.unify(0, [], vhole(1), v32t, s1, s2) |> should.equal(Ok([#(1, v32t)]))
  c.unify(0, [#(0, v64t)], vhole(1), v32t, s1, s2)
  |> should.equal(Ok([#(1, v32t), #(0, v64t)]))
}

pub fn infer_var_test() {
  let ctx = [#("x", #(v32(1), v32t))]
  c.infer(0, ctx, [], [], var(0, s1)) |> should.equal(#(v32(1), v32t, [], []))
  c.infer(0, ctx, [], [], var(1, s1))
  |> should.equal(#(c.VErr, c.VErr, [], [c.VarUndefined(1, s1)]))
}

pub fn check_var_test() {
  let ctx = [#("x", #(v32(1), v32t))]
  c.check(0, ctx, [], [], var(0, s1), v32t, s2)
  |> should.equal(#(v32(1), [], []))
  c.check(0, ctx, [], [], var(1, s1), v32t, s2)
  |> should.equal(#(c.VErr, [], [c.VarUndefined(1, s1)]))
  c.check(0, ctx, [], [], var(0, s1), v64t, s2)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(v32t, v64t, s1, s2)]))
}

// --- Hole --- \\
pub fn eval_hole_test() {
  c.eval([], hole(0, s1)) |> should.equal(vhole(0))
  c.eval([], hole(1, s1)) |> should.equal(vhole(1))
}

pub fn infer_hole_test() {
  c.infer(0, [], [], [], hole(0, s1))
  |> should.equal(#(c.VErr, c.VErr, [], [c.TypeAnnotationNeeded(hole(0, s1))]))
}

pub fn check_hole_test() {
  c.check(0, [], [], [], hole(0, s1), v32t, s2)
  |> should.equal(#(vhole(0), [], []))
}

// --- Ctr --- \\
pub fn eval_ctr_test() {
  c.eval([], ctr("A", i32(1, s1), s2)) |> should.equal(c.VCtr("A", v32(1)))
}

pub fn unify_ctr_tag_test() {
  c.unify(0, [], c.VCtr("A", v32(1)), c.VCtr("A", v32(1)), s1, s2)
  |> should.equal(Ok([]))
  c.unify(0, [], c.VCtr("A", v32(1)), c.VCtr("B", v32(1)), s1, s2)
  |> should.equal(
    Error(c.TypeMismatch(c.VCtr("A", v32(1)), c.VCtr("B", v32(1)), s1, s2)),
  )
}

// TODO: check_ctr_def_test
// TODO: check_type_test
// TODO: ctr_solve_params_test

pub fn infer_ctr_test() {
  c.infer(0, [], [], [], ctr("A", i32(1, s1), s2))
  |> should.equal(#(c.VErr, c.VErr, [], [c.CtrUndefined("A", s2)]))

  let tenv = [#("A", c.CtrDef([], i32t(s1), i64t(s2)))]
  c.infer(0, [], tenv, [], ctr("A", i32(1, s3), s4))
  |> should.equal(#(c.VCtr("A", v32(1)), v64t, [], []))
}

pub fn infer_ctr_arg_bind_test() {
  let tenv = [#("A", c.CtrDef(["a"], var(0, s1), var(0, s2)))]
  c.infer(0, [], tenv, [], ctr("A", i32(1, s3), s4))
  |> should.equal(#(c.VCtr("A", v32(1)), v32t, [#(0, v32t)], []))
}

pub fn infer_ctr_arg_mismatch_test() {
  let tenv = [#("A", c.CtrDef([], i32t(s1), i64t(s2)))]
  c.infer(0, [], tenv, [], ctr("A", typ(0, s3), s4))
  |> should.equal(
    #(c.VCtr("A", c.VTyp(0)), v64t, [], [
      c.TypeMismatch(c.VTyp(1), v32t, s3, s1),
    ]),
  )
}

pub fn infer_ctr_arg_unsolved_test() {
  let ctr_def = c.CtrDef(["a"], i32t(s1), var(0, s2))
  let tenv = [#("A", ctr_def)]
  c.infer(0, [], tenv, [], ctr("A", i32(1, s3), s4))
  |> should.equal(
    #(c.VCtr("A", v32(1)), vhole(0), [], [
      c.CtrUnsolvedParam("A", ctr_def, 0, s4),
    ]),
  )
}

pub fn check_ctr_test() {
  c.check(0, [], [], [], ctr("A", i32(1, s1), s2), v32t, s2)
  |> should.equal(#(c.VErr, [], [c.CtrUndefined("A", s2)]))

  let tenv = [#("A", c.CtrDef([], i32t(s1), i64t(s2)))]
  c.check(0, [], tenv, [], ctr("A", i32(1, s3), s4), v64t, s5)
  |> should.equal(#(c.VCtr("A", v32(1)), [], []))
}

pub fn check_ctr_arg_mismatch_test() {
  let tenv = [#("A", c.CtrDef([], i32t(s1), i64t(s2)))]
  c.check(0, [], tenv, [], ctr("A", i64(1, s3), s4), v64t, s5)
  |> should.equal(
    #(c.VCtr("A", c.VErr), [], [c.TypeMismatch(v64t, v32t, s3, s1)]),
  )
}

pub fn check_ctr_arg_unsolved_test() {
  let ctr_def = c.CtrDef(["a"], var(0, s1), i64t(s2))
  let tenv = [#("A", ctr_def)]
  c.check(0, [], tenv, [], ctr("A", i32(1, s3), s4), v64t, s5)
  |> should.equal(
    #(c.VCtr("A", v32(1)), [#(0, v32t)], [
      c.CtrUnsolvedParam("A", ctr_def, 0, s4),
    ]),
  )
}

pub fn check_ctr_ret_bind_test() {
  let tenv = [#("A", c.CtrDef(["a"], var(0, s1), var(0, s2)))]
  c.check(0, [], tenv, [], ctr("A", i32(1, s3), s4), v32t, s5)
  |> should.equal(#(c.VCtr("A", v32(1)), [#(0, v32t)], []))
}

pub fn check_ctr_ret_mismatch_test() {
  let tenv = [#("A", c.CtrDef([], i32t(s1), i64t(s2)))]
  c.check(0, [], tenv, [], ctr("A", i32(1, s3), s4), v32t, s5)
  |> should.equal(
    #(c.VCtr("A", v32(1)), [], [c.TypeMismatch(v64t, v32t, s2, s5)]),
  )
}

// --- Rcd --- \\
pub fn eval_rcd_test() {
  c.eval([], rcd([], s0)) |> should.equal(c.VRcd([]))
  c.eval([], rcd([#("a", i32t(s1))], s0))
  |> should.equal(c.VRcd([#("a", v32t)]))
  c.eval([], rcd([#("a", i32t(s1)), #("b", i64t(s2))], s0))
  |> should.equal(c.VRcd([#("a", v32t), #("b", v64t)]))
}

pub fn unify_rcd_missing_test() {
  let ab = c.VRcd([#("a", v32t), #("b", v64t)])
  c.unify(0, [], ab, c.VRcd([]), s1, s2)
  |> should.equal(Error(c.RcdMissingFields(["a", "b"], s2)))
  c.unify(0, [], c.VRcd([]), ab, s1, s2)
  |> should.equal(Error(c.RcdMissingFields(["a", "b"], s1)))
}

pub fn unify_rcd_mismatch_test() {
  c.unify(0, [], c.VRcd([#("a", v32t)]), c.VRcd([#("a", v64t)]), s1, s2)
  |> should.equal(Error(c.TypeMismatch(v32t, v64t, s1, s2)))
}

pub fn unify_rcd_order_test() {
  let ab = c.VRcd([#("a", v32t), #("b", v64t)])
  let ba = c.VRcd([#("b", v64t), #("a", v32t)])
  c.unify(0, [], ab, ab, s1, s2) |> should.equal(Ok([]))
  c.unify(0, [], ab, ba, s1, s2) |> should.equal(Ok([]))
}

pub fn unify_rcd_bind_test() {
  let a = c.VRcd([#("a", v32t)])
  let b = c.VRcd([#("a", vhole(1))])
  c.unify(0, [], a, b, s1, s2) |> should.equal(Ok([#(1, v32t)]))
}

pub fn infer_rcd_test() {
  c.infer(0, [], [], [], rcd([], s0))
  |> should.equal(#(c.VRcd([]), c.VRcd([]), [], []))
  c.infer(0, [], [], [], rcd([#("a", i32(1, s1))], s0))
  |> should.equal(#(c.VRcd([#("a", v32(1))]), c.VRcd([#("a", v32t)]), [], []))
  c.infer(0, [], [], [], rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0))
  |> should.equal(
    #(
      c.VRcd([#("a", v32(1)), #("b", v64(2))]),
      c.VRcd([#("a", v32t), #("b", v64t)]),
      [],
      [],
    ),
  )
}

pub fn check_rcd_test() {
  c.check(0, [], [], [], rcd([], s0), c.VRcd([]), s2)
  |> should.equal(#(c.VRcd([]), [], []))
  let ty = c.VRcd([#("a", v32t)])
  c.check(0, [], [], [], rcd([#("a", i32(1, s1))], s0), ty, s2)
  |> should.equal(#(c.VRcd([#("a", v32(1))]), [], []))
}

pub fn check_rcd_missing_test() {
  let term = rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0)
  c.check(0, [], [], [], term, c.VRcd([]), s2)
  |> should.equal(#(c.VErr, [], [c.RcdMissingFields(["a", "b"], s2)]))
  let ty = c.VRcd([#("a", v32t), #("b", v64t)])
  c.check(0, [], [], [], rcd([], s1), ty, s2)
  |> should.equal(#(c.VErr, [], [c.RcdMissingFields(["a", "b"], s1)]))
}

pub fn check_rcd_mismatch_test() {
  let term = rcd([#("a", i32(1, s1))], s0)
  c.check(0, [], [], [], term, c.VRcd([#("a", v64t)]), s2)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(v32t, v64t, s0, s2)]))
}

pub fn check_rcd_order_test() {
  let term = rcd([#("b", i64(2, s1)), #("a", i32(1, s2))], s0)
  let typ = c.VRcd([#("a", v32t), #("b", v64t)])
  c.check(0, [], [], [], term, typ, s3)
  |> should.equal(#(c.VRcd([#("b", v64(2)), #("a", v32(1))]), [], []))
}

// --- Dot --- \\
pub fn eval_dot_test() {
  c.eval([], dot(i32(1, s1), "a", s2))
  |> should.equal(c.VErr)
  c.eval([], dot(rcd([], s0), "a", s1))
  |> should.equal(c.VErr)
  c.eval([], dot(rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0), "a", s3))
  |> should.equal(v32(1))
  c.eval([], dot(rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0), "b", s3))
  |> should.equal(v64(2))
  c.eval([vvar(0)], dot(var(0, s1), "a", s2))
  |> should.equal(c.VNeut(c.HVar(0), [c.EDot("a")]))
  c.eval([vhole(0)], dot(var(0, s1), "a", s2))
  |> should.equal(c.VNeut(c.HHole(0), [c.EDot("a")]))
}

pub fn infer_dot_non_ctr_test() {
  c.infer(0, [], [], [], dot(i32(1, s1), "x", s2))
  |> should.equal(#(c.VErr, c.VErr, [], [c.DotOnNonCtr(v32t, "x", s1)]))
}

pub fn infer_dot_record_test() {
  let record = rcd([#("x", i32(1, s1)), #("y", i64(2, s2))], s0)
  c.infer(0, [], [], [], dot(record, "x", s3))
  |> should.equal(#(v32(1), v32t, [], []))

  c.infer(0, [], [], [], dot(record, "y", s3))
  |> should.equal(#(v64(2), v64t, [], []))
}

pub fn infer_dot_record_not_found_test() {
  c.infer(0, [], [], [], dot(rcd([], s0), "x", s1))
  |> should.equal(#(c.VErr, c.VErr, [], [c.DotFieldNotFound("x", [], s0)]))
}

pub fn check_dot_test() {
  let ab = rcd([#("a", i32(1, s1)), #("b", i64(2, s2))], s0)
  c.check(0, [], [], [], dot(ab, "a", s3), v32t, s2)
  |> should.equal(#(v32(1), [], []))
  c.check(0, [], [], [], dot(ab, "b", s3), v64t, s2)
  |> should.equal(#(v64(2), [], []))
}

// --- Ann --- \\
pub fn eval_ann_test() {
  let env = [v32(1)]
  c.eval(env, ann(var(0, s1), typ(1, s2), s3)) |> should.equal(v32(1))
}

pub fn infer_ann_test() {
  c.infer(0, [], [], [], ann(i32(1, s1), i32t(s2), s3))
  |> should.equal(#(v32(1), v32t, [], []))
}

pub fn infer_ann_mismatch_test() {
  c.infer(1, [], [], [], ann(i32(1, s1), i64t(s2), s3))
  |> should.equal(#(c.VErr, v64t, [], [c.TypeMismatch(v32t, v64t, s1, s2)]))
}

pub fn check_ann_test() {
  c.check(0, [], [], [], ann(i32(1, s1), i32t(s2), s3), v32t, s2)
  |> should.equal(#(v32(1), [], []))
}

pub fn check_ann_mismatch_test() {
  c.check(0, [], [], [], ann(i32(1, s1), i32t(s2), s3), v64t, s4)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(v32t, v64t, s3, s4)]))
}

// --- Lam --- \\
pub fn eval_lam_test() {
  c.eval([], lam("x", var(0, s1), s2))
  |> should.equal(c.VLam("x", [], var(0, s1)))
}

pub fn lam_infer_test() {
  let term = lam("x", var(0, s1), s2)
  c.infer(0, [], [], [], term)
  |> should.equal(#(c.VErr, c.VErr, [], [c.TypeAnnotationNeeded(term)]))
}

pub fn check_lam_test() {
  let term = lam("x", var(0, s1), s2)
  c.check(0, [], [], [], term, c.VPi("x", [], c.VTyp(0), typ(0, s3)), s4)
  |> should.equal(#(c.VLam("x", [], var(0, s1)), [], []))
}

pub fn check_lam_mismatch_test() {
  let term = lam("x", var(0, s1), s2)
  c.check(0, [], [], [], term, c.VTyp(0), s3)
  |> should.equal(#(c.VErr, [], [c.TypeAnnotationNeeded(term)]))
}

// --- Pi --- \\
pub fn eval_pi_test() {
  c.eval([], pi("x", i32t(s1), var(0, s2), s3))
  |> should.equal(c.VPi("x", [], v32t, var(0, s2)))
}

pub fn infer_pi_test() {
  c.infer(0, [], [], [], pi("x", i32t(s1), var(0, s2), s3))
  |> should.equal(#(c.VPi("x", [], v32t, var(0, s2)), c.VTyp(0), [], []))
}

pub fn infer_pi_undefined_test() {
  c.infer(0, [], [], [], pi("x", var(1, s1), var(2, s2), s3))
  |> should.equal(
    #(c.VPi("x", [], c.VErr, var(2, s2)), c.VTyp(0), [], [
      c.VarUndefined(1, s1),
      c.VarUndefined(2, s2),
    ]),
  )
}

pub fn check_pi_test() {
  let term = pi("x", i32t(s1), var(0, s2), s3)
  c.check(0, [], [], [], term, c.VTyp(0), s4)
  |> should.equal(#(c.VPi("x", [], v32t, var(0, s2)), [], []))
}

pub fn check_pi_mismatch_test() {
  let term = pi("x", i32t(s1), var(0, s2), s3)
  c.check(0, [], [], [], term, c.VTyp(1), s4)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(c.VTyp(0), c.VTyp(1), s3, s4)]))
}

// --- App --- \\
pub fn eval_app_value_test() {
  c.eval_app(c.VTyp(0), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VLit(c.I32(0)), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VLitT(c.I32T), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VNeut(c.HVar(0), [c.EDot("x")]), v32(1))
  |> should.equal(c.VNeut(c.HVar(0), [c.EDot("x"), c.EApp(v32(1))]))
  c.eval_app(c.VNeut(c.HHole(0), [c.EDot("x")]), v32(1))
  |> should.equal(c.VNeut(c.HHole(0), [c.EDot("x"), c.EApp(v32(1))]))
  c.eval_app(c.VCtr("A", v64t), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VRcd([]), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VLam("x", [], i64(0, s1)), v32(1)) |> should.equal(v64(0))
  c.eval_app(c.VLam("x", [], var(0, s1)), v32(1)) |> should.equal(v32(1))
  c.eval_app(c.VPi("x", [], v32t, i64t(s1)), v32(1)) |> should.equal(c.VErr)
  c.eval_app(c.VErr, v32(1)) |> should.equal(c.VErr)
}

pub fn eval_app_test() {
  let fun = lam("x", var(0, s1), s2)
  c.eval([], app(fun, i32(1, s3), s4)) |> should.equal(v32(1))
}

pub fn infer_app_test() {
  let ty = c.VPi("x", [], v32t, i64t(s0))
  let ctx = [#("f", #(c.VLam("x", [], i64(2, s1)), ty))]
  c.infer(0, ctx, [], [], var(0, s2))
  |> should.equal(#(c.VLam("x", [], i64(2, s1)), ty, [], []))
  c.infer(0, ctx, [], [], app(var(0, s1), i32(1, s2), s3))
  |> should.equal(#(v64(2), v64t, [], []))
  c.infer(0, ctx, [], [], app(var(0, s1), i64(1, s2), s3))
  |> should.equal(#(v64(2), v64t, [], [c.TypeMismatch(v64t, v32t, s2, s1)]))
}

pub fn check_app_test() {
  let ty = c.VPi("x", [], v32t, i64t(s0))
  let ctx = [#("f", #(c.VLam("x", [], i64(2, s1)), ty))]
  c.check(0, ctx, [], [], app(var(0, s2), i32(1, s3), s4), v64t, s2)
  |> should.equal(#(v64(2), [], []))
  c.check(0, ctx, [], [], app(var(0, s2), i32(1, s3), s4), v32t, s2)
  |> should.equal(#(c.VErr, [], [c.TypeMismatch(v64t, v32t, s4, s2)]))
}

// --- Match --- \\
// TODO: eval_match_value_test
// TODO: eval_match_test

// pub fn match_pattern_any_test() {
//   c.match_pattern(c.PAny, v32(1)) |> should.equal(Ok([]))
// }

// pub fn match_pattern_as_test() {
//   c.match_pattern(pvar("a"), v32(1)) |> should.equal(Ok([v32(1)]))
// }

// pub fn match_pattern_typ_test() {
//   c.match_pattern(c.PTyp(0), c.VTyp(0)) |> should.equal(Ok([]))
//   c.match_pattern(c.PTyp(0), c.VTyp(1)) |> should.equal(Error(Nil))
// }

// pub fn match_pattern_lit_test() {
//   c.match_pattern(c.PLit(c.I32(1)), v32(1)) |> should.equal(Ok([]))
//   c.match_pattern(c.PLit(c.I32(1)), v32(2)) |> should.equal(Error(Nil))
// }

// pub fn match_pattern_ctr_test() {
//   c.match_pattern(c.PCtr("A", pvar("x")), c.VCtr("A", v32(1)))
//   |> should.equal(Ok([v32(1)]))
//   c.match_pattern(c.PCtr("A", pvar("x")), c.VCtr("B", v32(1)))
//   |> should.equal(Error(Nil))
// }

// pub fn match_pattern_rcd_test() {
//   c.match_pattern(c.PRcd([#("x", pvar("a"))]), c.VRcd([#("x", v32(1))]))
//   |> should.equal(Ok([v32(1)]))
//   c.match_pattern(
//     c.PRcd([#("x", pvar("a")), #("y", pvar("b"))]),
//     c.VRcd([#("x", v32(1)), #("y", v64(2))]),
//   )
//   |> should.equal(Ok([v32(1), v64(2)]))
// }

// pub fn match_pattern_bad_test() {
//   c.match_pattern(c.PTyp(0), c.VBad(c.VTyp(0), [])) |> should.equal(Ok([]))
// }

// pub fn eval_match_test() {
//   c.eval([], match(i32(1), [case_(c.PAny, i64(2))]))
//   |> should.equal(v64(2))

//   let env = [c.VNeut(c.HVar(0), [])]
//   let cases = [case_(c.PAny, i32(1))]
//   c.eval(env, match(var(0), cases))
//   |> should.equal(c.VNeut(c.HVar(0), [c.EMatch(env, cases)]))
// }

// pub fn bind_pattern_any_test() {
//   c.bind_pattern(0, [], [], c.PAny, v32t, s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_as_test() {
//   c.bind_pattern(0, [], [], pvar("x"), v32t, s, s2)
//   |> should.equal(#(1, [#("x", #(hvar(0), v32t))], []))
// }

// pub fn bind_pattern_typ_test() {
//   c.bind_pattern(0, [], [], c.PTyp(0), c.VTyp(0), s, s2)
//   |> should.equal(#(0, [], [c.TypeMismatch(c.VTyp(1), c.VTyp(0), s, s2)]))
//   c.bind_pattern(0, [], [], c.PTyp(0), c.VTyp(1), s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_lit_test() {
//   c.bind_pattern(0, [], [], c.PLit(c.I32(1)), c.VTyp(0), s, s2)
//   |> should.equal(#(0, [], [c.TypeMismatch(v32t, c.VTyp(0), s, s2)]))
//   c.bind_pattern(0, [], [], c.PLit(c.I32(1)), v32t, s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_ctr_test() {
//   let p = c.PCtr("A", c.PAny)
//   c.bind_pattern(0, [], [], p, v32t, s, s2)
//   |> should.equal(#(0, [], [c.CtrUndefined("A", s)]))
//   let tenv = [#("A", c.CtrDef([], i32t, i64t))]
//   c.bind_pattern(0, [], tenv, p, v32t, s, s2)
//   |> should.equal(#(0, [], [c.TypeMismatch(v64t, v32t, s, s)]))
//   c.bind_pattern(0, [], tenv, p, v64t, s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_rcd_test() {
//   c.bind_pattern(0, [], [], c.PRcd([]), c.VRcd([]), s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_rcd_unused_test() {
//   let p = c.PRcd([])
//   let t = c.VRcd([#("a", v32t)])
//   c.bind_pattern(0, [], [], p, t, s, s2)
//   |> should.equal(#(0, [], []))
// }

// pub fn bind_pattern_rcd_missing_test() {
//   let p = c.PRcd([#("a", pvar("x"))])
//   let t = c.VRcd([])
//   c.bind_pattern(0, [], [], p, t, s, s2)
//   |> should.equal(
//     #(1, [#("x", #(hvar(0), hhole(0)))], [c.RcdMissingFields(["a"], s2)]),
//   )
// }

// pub fn match_infer_test() {
//   c.infer(0, [], [], match(i32(1), []))
//   |> should.equal(c.VErr(c.MatchEmpty(v32t, s)))

//   c.infer(0, [], [], match(i32(1), [case_(c.PAny, i64(2))]))
//   |> should.equal(v64t)

//   let term = match(i32(1), [case_(c.PAny, i64_2(2)), case_(c.PAny, typ(0))])
//   c.infer(0, [], [], term)
//   |> should.equal(c.VBad(v64t, [c.TypeMismatch(c.VTyp(1), v64t, s, s2)]))

//   c.infer(0, [], [], match(i32(1), [case_(pvar("a"), var(0))]))
//   |> should.equal(v32t)
// }

// pub fn match_check_test() {
//   c.check(0, [], [], match(i32(1), []), v64t, s2)
//   |> should.equal(c.VErr(c.MatchEmpty(v32t, s)))

//   c.check(0, [], [], match(i32(1), [case_(c.PAny, i64(2))]), v64t, s2)
//   |> should.equal(v64t)

//   let term = match(i32(1), [case_(c.PAny, i64(2))])
//   c.check(0, [], [], term, c.VTyp(0), s2)
//   |> should.equal(c.VErr(c.TypeMismatch(v64t, c.VTyp(0), s, s2)))

//   let term = match(i32(1), [case_(c.PAny, i64_2(2)), case_(c.PAny, typ(0))])
//   c.check(0, [], [], term, v64t, s2)
//   |> should.equal(c.VBad(v64t, [c.TypeMismatch(c.VTyp(1), v64t, s, s2)]))

//   let term = match(i32(1), [case_(c.PAny, i64(2)), case_(c.PAny, typ(0))])
//   c.check(0, [], [], term, c.VTyp(2), s2)
//   |> should.equal(c.VErr(c.TypeMismatch(v64t, c.VTyp(2), s, s2)))

//   c.check(0, [], [], match(i32(1), [case_(pvar("a"), var(0))]), v32t, s2)
//   |> should.equal(v32t)

//   c.check(0, [], [], match(i32(1), [case_(pvar("a"), var(0))]), v64t, s2)
//   |> should.equal(c.VErr(c.TypeMismatch(v32t, v64t, s, s2)))
// }

// // --- Bad --- \\
// // TODO

// // --- Err --- \\
// // TODO

// --- HELPERS to make writing ASTs less painful ---
const s0 = c.Span("core_test", 0, 0)

const s1 = c.Span("core_test", 1, 1)

const s2 = c.Span("core_test", 2, 2)

const s3 = c.Span("core_test", 3, 3)

const s4 = c.Span("core_test", 4, 4)

const s5 = c.Span("core_test", 5, 5)

const s6 = c.Span("core_test", 6, 6)

const s7 = c.Span("core_test", 7, 7)

fn typ(l, s) {
  c.Term(c.Typ(l), s)
}

fn lit(v, s) {
  c.Term(c.Lit(v), s)
}

fn litt(t, s) {
  c.Term(c.LitT(t), s)
}

fn i32(v, s) {
  lit(c.I32(v), s)
}

fn i64(v, s) {
  lit(c.I64(v), s)
}

fn v32(v) {
  c.VLit(c.I32(v))
}

fn v64(v) {
  c.VLit(c.I64(v))
}

fn i32t(s) {
  c.Term(c.LitT(c.I32T), s)
}

const v32t = c.VLitT(c.I32T)

fn i64t(s) {
  c.Term(c.LitT(c.I64T), s)
}

const v64t = c.VLitT(c.I64T)

fn var(i, s) {
  c.Term(c.Var(i), s)
}

fn hole(id, s) {
  c.Term(c.Hole(id), s)
}

fn ctr(k, arg, s) {
  c.Term(c.Ctr(k, arg), s)
}

fn rcd(fields, s) {
  c.Term(c.Rcd(fields), s)
}

fn dot(arg, name, s) {
  c.Term(c.Dot(arg, name), s)
}

fn pi(name, in, out, s) {
  c.Term(c.Pi(name, in, out), s)
}

fn lam(name, body, s) {
  c.Term(c.Lam(name, body), s)
}

fn ann(x, t, s) {
  c.Term(c.Ann(x, t), s)
}

fn app(f, a, s) {
  c.Term(c.App(f, a), s)
}

fn match(arg, cases, s) {
  c.Term(c.Match(arg, cases), s)
}

fn case_(p, b, s) {
  c.Case(p, b, s)
}

fn pvar(x) {
  c.PAs(c.PAny, x)
}

fn vvar(i) {
  c.VNeut(c.HVar(i), [])
}

fn vhole(i) {
  c.VNeut(c.HHole(i), [])
}
