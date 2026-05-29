/// Tests for the eval module — Core evaluator.
///
/// These tests verify:
/// - Basic value constructors (Typ, Hole, Lit, LitT)
/// - Variable lookup
/// - Constructor evaluation
/// - Record and record type evaluation
/// - Call evaluation
/// - Annotation evaluation
/// - Lambda and Pi evaluation
/// - Fix evaluation
/// - Application (beta reduction, implicit expansion, neutral)
/// - Match evaluation
/// - Pattern matching
import core/term.{type Case, type Pattern, type Term} as tm
import core/context.{type FFI}
import core/eval.{eval, match_pattern}
import core/literals.{type Literal} as lit
import core/value.{type Env, type Value} as v
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("eval_test", 0, 0, 0, 0)

pub fn eval_typ_test() {
  let term = tm.Typ(0)
  let result = eval([], [], term)
  assert result == v.Typ(0)
}

pub fn eval_hole_test() {
  let term = tm.Hole(0)
  let result = eval([], [], term)
  assert result == v.hole(0)
}

pub fn eval_lit_test() {
  let term = tm.Lit(lit.Int(1))
  let result = eval([], [], term)
  assert result == v.int(1)
}

pub fn eval_litt_test() {
  let term = tm.LitT(lit.IntT)
  let result = eval([], [], term)
  assert result == v.int_t
}

pub fn eval_var_undefined_test() {
  let term = tm.Var(0)
  let result = eval([], [], term)
  assert result == v.Err
}

pub fn eval_var0_test() {
  let term = tm.Var(0)
  let env = [v.int_t, v.float_t]
  let result = eval([], env, term)
  assert result == v.int_t
}

pub fn eval_var1_test() {
  let term = tm.Var(1)
  let env = [v.int_t, v.float_t]
  let result = eval([], env, term)
  assert result == v.float_t
}

pub fn eval_ctr_test() {
  let term = tm.Ctr("A", tm.LitT(lit.IntT))
  let result = eval([], [], term)
  assert result == v.Ctr("A", v.int_t)
}

pub fn eval_rcd_empty_test() {
  let term = tm.Rcd([])
  let result = eval([], [], term)
  assert result == v.Rcd([])
}

pub fn eval_rcd_fields_test() {
  let term = tm.Rcd([
    #("x", tm.LitT(lit.IntT)),
    #("y", tm.LitT(lit.FloatT)),
  ])
  let result = eval([], [], term)
  assert result == v.Rcd([
    #("x", v.int_t),
    #("y", v.float_t),
  ])
}

pub fn eval_rcdt_empty_test() {
  let term = tm.RcdT([])
  let result = eval([], [], term)
  assert result == v.RcdT([])
}

pub fn eval_rcdt_fields_test() {
  let term =
    tm.RcdT([
      #("x", tm.LitT(lit.IntT), Some(tm.Lit(lit.Int(42)))),
      #("y", tm.LitT(lit.FloatT), None),
    ])
  let result = eval([], [], term)
  assert result
    == v.RcdT([
      #("x", v.int_t, Some(v.int(42))),
      #("y", v.float_t, None),
    ])
}

pub fn eval_call_undefined_test() {
  let term = tm.Call("f", [], tm.LitT(lit.IntT))
  let result = eval([], [], term)
  assert result == v.call("f", [])
}

pub fn eval_call_return_none_test() {
  let ffi: FFI = [#("f", fn(_) { None })]
  let term = tm.Call("f", [], tm.LitT(lit.IntT))
  let result = eval(ffi, [], term)
  assert result == v.call("f", [])
}

pub fn eval_call_return_some_test() {
  let ffi: FFI = [#("f", fn(_) { Some(v.int(42)) })]
  let term = tm.Call("f", [], tm.LitT(lit.IntT))
  let result = eval(ffi, [], term)
  assert result == v.int(42)
}

pub fn eval_call_args_test() {
  let term =
    tm.Call("f", [tm.Lit(lit.Int(42)), tm.Lit(lit.Float(3.14))], tm.LitT(lit.IntT))
  let result = eval([], [], term)
  assert result == v.call("f", [v.int(42), v.float(3.14)])
}

pub fn eval_ann_test() {
  let term = tm.Ann(tm.Lit(lit.Int(42)), tm.LitT(lit.IntT))
  let result = eval([], [], term)
  assert result == v.int(42)
}

pub fn eval_lam_explicit_test() {
  // $fn(x: $Int) => x
  let term = tm.Lam(False, #("x", tm.LitT(lit.IntT)), tm.Var(0))
  let result = eval([], [], term)
  assert result == v.Lam(False, #("x", v.int_t), #([], tm.Var(0)))
}

pub fn eval_lam_implicit_test() {
  // $fn<x: $Type> => x
  let term = tm.Lam(True, #("x", tm.LitT(lit.IntT)), tm.Var(0))
  let result = eval([], [], term)
  assert result == v.Lam(True, #("x", v.int_t), #([], tm.Var(0)))
}

pub fn eval_lam_closure_test() {
  // let a = $Int; $fn(x: a) => a
  let term = tm.Lam(False, #("x", tm.Var(0)), tm.Var(1))
  let env = [v.int_t]
  let result = eval([], env, term)
  assert result == v.Lam(False, #("x", v.int_t), #(env, tm.Var(1)))
}

pub fn eval_pi_explicit_test() {
  // $pi(x: $Int) => x
  let term = tm.Pi(False, #("x", tm.LitT(lit.IntT)), tm.Var(0))
  let result = eval([], [], term)
  assert result == v.Pi(False, #("x", v.int_t), #([], tm.Var(0)))
}

pub fn eval_pi_implicit_test() {
  // $pi<x: $Int> => x
  let term = tm.Pi(True, #("x", tm.LitT(lit.IntT)), tm.Var(0))
  let result = eval([], [], term)
  assert result == v.Pi(True, #("x", v.int_t), #([], tm.Var(0)))
}

pub fn eval_pi_closure_test() {
  // let a = $Int; $pi(x: a) => a
  let term = tm.Pi(False, #("x", tm.Var(0)), tm.Var(1))
  let env = [v.int_t]
  let result = eval([], env, term)
  assert result == v.Pi(False, #("x", v.int_t), #(env, tm.Var(1)))
}

pub fn eval_fix_test() {
  let term = tm.Fix("f", tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.Fix("f", #([], tm.Lit(lit.Int(42))))
}

pub fn eval_app_not_a_function_test() {
  let fun = tm.Typ(0)
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.Err
}

pub fn eval_app_neutral_test() {
  // ?10 42 ~> ?10 42
  let fun = tm.Hole(10)
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.app(v.NHole(10), v.int(42))
}

pub fn eval_app_beta_reduction_test() {
  // ($fn(x: $Int) => x) 42 ~> 42
  let fun = tm.Lam(False, #("x", tm.LitT(lit.IntT)), tm.Var(0))
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.int(42)
}

pub fn eval_app_implicit_expansion_test() {
  // ($fn<x: $Type> => ?10 x) 42
  // ~> (?10 $error) 42
  let inner = tm.App(tm.Hole(10), tm.Var(0))
  let fun = tm.Lam(True, #("x", tm.Typ(0)), inner)
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.app(
    v.NApp(v.NHole(10), v.Err),
    v.int(42),
  )
}

// TypeDef( params: List(#(String, Term)), constructors: List(#(String, #(List(String), Term, Term), Span)), span: Span, )

pub fn eval_match_empty_test() {
  let term = tm.Match(tm.Lit(lit.Int(42)), [])
  let result = eval([], [], term)
  assert result == v.Err
}

pub fn eval_match_first_test() {
  // Match first case with no bindings, base test
  // $match (42) { | 42 => 1.0 }
  let cases = [
    tm.Case(tm.PLit(lit.Int(42)), None, tm.float(1.0))
  ]
  let term = tm.Match(tm.Lit(lit.Int(42)), cases)
  let result = eval([], [], term)
  assert result == v.float(1.0)
}

pub fn eval_match_second_test() {
  // Match second case with no bindings, inductive test
  // $match (42) { | 0 => 1.0 | 42 => 2.0 }
  let cases = [
    tm.Case(tm.PLit(lit.Int(0)), None, tm.float(1.0)),
    tm.Case(tm.PLit(lit.Int(42)), None, tm.float(2.0)),
  ]
  let term = tm.Match(tm.Lit(lit.Int(42)), cases)
  let result = eval([], [], term)
  assert result == v.float(2.0)
}

pub fn eval_match_bindings_test() {
  // Match case with 2 bindings, DeBruijn/env test
  // $match {x: 10, y: 20} { | {x: a, y: b} => {x: a, y: b} }
  //    a is #1 = 10, b is #0 = 20
  let arg = tm.Rcd([
    #("x", tm.Lit(lit.Int(10))),
    #("y", tm.Lit(lit.Int(20))),
  ])
  let cases = [
    tm.Case(
      tm.PRcd([
        #("x", tm.PAlias("a", tm.PAny)),
        #("y", tm.PAlias("b", tm.PAny)),
      ]),
      None,
      tm.Rcd([
        #("x", tm.Var(1)),
        #("y", tm.Var(0)),
      ]),
    ),
  ]
  let term = tm.Match(arg, cases)
  let result = eval([], [], term)
  assert result == v.Rcd([
    #("x", v.int(10)),
    #("y", v.int(20)),
  ])
}

pub fn eval_match_guard_fail_test() {
  // Match case pattern but fail guard pattern
  // $match (42) { | x ? x ~ 0 => 1.0 | _ => 2.0 }
  let term =
    tm.Match(
      tm.Lit(lit.Int(42)),
      [
        tm.Case(
          tm.PAlias("x", tm.PAny),
          Some(#(tm.Var(0), tm.PLit(lit.Int(0)))),
          tm.float(1.0),
        ),
        tm.Case(tm.PAny, None, tm.float(2.0))
      ],
    )
  let result = eval([], [], term)
  assert result == v.float(2.0)
}

pub fn eval_match_guard_pass_test() {
  // Match both case and guard patterns
  // $match (42) { | x ? x ~ 42 => 1.0 | _ => 2.0 }
  let term =
    tm.Match(
      tm.Lit(lit.Int(42)),
      [
        tm.Case(
          tm.PAlias("x", tm.PAny),
          Some(#(tm.Var(0), tm.PLit(lit.Int(42)))),
          tm.float(1.0),
        ),
        tm.Case(tm.PAny, None, tm.float(2.0))
      ],
    )
  let result = eval([], [], term)
  assert result == v.float(1.0)
}

pub fn eval_match_guard_bindings_test() {
  // Match case with 1 binding and guard with 2 bindings
  // $match (10) { | x ? {x: 20, y: 30} ~ {x: a, y: b} => {x: x, y: a, z: b} }
  //    x is #2 = 10, a is #1 = 20, b is #0 = 30
  let cases = [
    tm.Case(
      tm.PAlias("x", tm.PAny),
      Some(#(
        tm.Rcd([
          #("x", tm.Lit(lit.Int(20))),
          #("y", tm.Lit(lit.Int(30))),
        ]),
        tm.PRcd([
          #("x", tm.PAlias("a", tm.PAny)),
          #("y", tm.PAlias("b", tm.PAny)),
        ]),
      )),
      tm.Rcd([
        #("x", tm.Var(2)),
        #("y", tm.Var(1)),
        #("z", tm.Var(0)),
      ]),
    ),
  ]
  let term = tm.Match(tm.Lit(lit.Int(10)), cases)
  let result = eval([], [], term)
  assert result
    == v.Rcd([
      #("x", v.int(10)),
      #("y", v.int(20)),
      #("z", v.int(30)),
    ])
}

pub fn eval_err_test() {
  let term = tm.Err
  let result = eval([], [], term)
  assert result == v.Err
}

// ============================================================================
// match_pattern tests
// ============================================================================

pub fn match_pattern_any_test() {
  // PAny matches any value
  let result = match_pattern(tm.PAny, v.int(42))
  assert result == Some([])
}

pub fn match_pattern_any_mismatch_test() {
  // PAny still matches even when value doesn't exist (returns None is wrong, PAny always matches)
  let result = match_pattern(tm.PAny, v.float(3.14))
  assert result == Some([])
}

pub fn match_pattern_typ_test() {
  // PTyp matches VTyp with same universe
  let result = match_pattern(tm.PTyp(0), v.Typ(0))
  assert result == Some([])
}

pub fn match_pattern_typ_mismatch_test() {
  // PTyp doesn't match VTyp with different universe
  let result = match_pattern(tm.PTyp(1), v.Typ(0))
  assert result == None
}

pub fn match_pattern_typ_wrong_value_test() {
  // PTyp doesn't match non-VTyp values
  let result = match_pattern(tm.PTyp(0), v.int(42))
  assert result == None
}

pub fn match_pattern_lit_int_test() {
  // PLit matches VLit with same Int literal
  let result = match_pattern(tm.PLit(lit.Int(42)), v.int(42))
  assert result == Some([])
}

pub fn match_pattern_lit_int_mismatch_test() {
  // PLit doesn't match VLit with different Int
  let result = match_pattern(tm.PLit(lit.Int(1)), v.int(42))
  assert result == None
}

pub fn match_pattern_lit_float_test() {
  // PLit matches VLit with same Float literal
  let result = match_pattern(tm.PLit(lit.Float(3.14)), v.float(3.14))
  assert result == Some([])
}

pub fn match_pattern_lit_wrong_value_test() {
  // PLit doesn't match non-VLit values
  let result = match_pattern(tm.PLit(lit.Int(42)), v.int(43))
  assert result == None
}

pub fn match_pattern_litt_int_test() {
  // PLitT matches VLitT with same literal type
  let result = match_pattern(tm.PLitT(lit.IntT), v.int_t)
  assert result == Some([])
}

pub fn match_pattern_litt_int_mismatch_test() {
  // PLitT(IntT) doesn't match VLitT(FloatT)
  let result = match_pattern(tm.PLitT(lit.IntT), v.float_t)
  assert result == None
}

pub fn match_pattern_litt_wrong_value_test() {
  // PLitT doesn't match non-VLitT values
  let result = match_pattern(tm.PLitT(lit.IntT), v.int(42))
  assert result == None
}

pub fn match_pattern_alias_test() {
  // PAlias binds the value and matches the inner pattern
  let result = match_pattern(
    tm.PAlias("x", tm.PAny),
    v.int(42),
  )
  assert result == Some([v.int(42)])
}

pub fn match_pattern_alias_nested_test() {
  // PAlias wrapping another PAlias, each alias binds the value, so 2 copies
  let result = match_pattern(
    tm.PAlias("outer", tm.PAlias("inner", tm.PAny)),
    v.int(42),
  )
  // Each PAlias prepends the value: inner binds it, then outer binds it again
  assert result == Some([v.int(42), v.int(42)])
}

pub fn match_pattern_alias_fail_test() {
  // PAlias fails if inner pattern fails
  let result = match_pattern(
    tm.PAlias("x", tm.PLit(lit.Int(0))),
    v.int(42),
  )
  assert result == None
}

pub fn match_pattern_ctr_test() {
  // PCtr matches VCtr with same tag, recurses into inner pattern
  let result = match_pattern(
    tm.PCtr("Some", tm.PAlias("x", tm.PAny)),
    v.Ctr("Some", v.int(42)),
  )
  assert result == Some([v.int(42)])
}

pub fn match_pattern_ctr_tag_mismatch_test() {
  // PCtr doesn't match VCtr with different tag
  let result = match_pattern(
    tm.PCtr("None", tm.PAny),
    v.Ctr("Some", v.int(42)),
  )
  assert result == None
}

pub fn match_pattern_ctr_wrong_value_test() {
  // PCtr doesn't match non-VCtr values
  let result = match_pattern(
    tm.PCtr("Some", tm.PAny),
    v.int(42),
  )
  assert result == None
}

pub fn match_pattern_ctr_nested_test() {
  // Nested PCtr: #Some(#Int(42))
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(42)))
  let result = match_pattern(
    tm.PCtr("Some", inner),
    v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
  )
  assert result == Some([])
}

pub fn match_pattern_ctr_nested_fail_test() {
  // Nested PCtr where inner literal doesn't match
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(99)))
  let result = match_pattern(
    tm.PCtr("Some", inner),
    v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
  )
  assert result == None
}

pub fn match_pattern_rcd_test() {
  // PRcd matches VRcd with same fields and matching values
  let result = match_pattern(
    tm.PRcd([
      #("x", tm.PLit(lit.Int(1))),
      #("y", tm.PAny),
    ]),
    v.Rcd([
      #("x", v.int(1)),
      #("y", v.int(2)),
    ]),
  )
  assert result == Some([])
}

pub fn match_pattern_rcd_extra_field_in_pattern_test() {
  // PRcd fails if pattern has field not in value
  let result = match_pattern(
    tm.PRcd([
      #("x", tm.PAny),
      #("y", tm.PAny),
      #("z", tm.PAny),
    ]),
    v.Rcd([
      #("x", v.int(1)),
      #("y", v.int(2)),
    ]),
  )
  assert result == None
}

pub fn match_pattern_rcd_fewer_fields_test() {
  // PRcd succeeds with fewer pattern fields than value fields
  let result = match_pattern(
    tm.PRcd([#("x", tm.PAny)]),
    v.Rcd([
      #("x", v.int(1)),
      #("y", v.int(2)),
    ]),
  )
  assert result == Some([])
}

pub fn match_pattern_rcd_with_bindings_test() {
  // PRcd with alias bindings
  let result = match_pattern(
    tm.PRcd([
      #("x", tm.PAlias("a", tm.PAny)),
      #("y", tm.PAlias("b", tm.PAny)),
      #("z", tm.PAlias("c", tm.PAny)),
    ]),
    v.Rcd([
      #("x", v.int(1)),
      #("y", v.int(2)),
      #("z", v.int(3)),
    ]),
  )
  // DeBruijn ordering: x is #2, y is #1, z is #0, so they bind like [z, y, z]
  assert result == Some([v.int(3), v.int(2), v.int(1)])
}

pub fn match_pattern_rcd_wrong_field_name_test() {
  // PRcd fails if pattern field name doesn't match value field name
  let result = match_pattern(
    tm.PRcd([#("x", tm.PAny)]),
    v.Rcd([#("y", v.int(1))]),
  )
  assert result == None
}

pub fn match_pattern_rcd_value_field_mismatch_test() {
  // PRcd fails if a field value doesn't match the pattern
  let result = match_pattern(
    tm.PRcd([#("x", tm.PLit(lit.Int(99)))]),
    v.Rcd([#("x", v.int(42))]),
  )
  assert result == None
}

pub fn match_pattern_error_test() {
  // PError matches VErr
  let result = match_pattern(tm.PError, v.Err)
  assert result == Some([])
}

pub fn match_pattern_error_wrong_value_test() {
  // PError doesn't match non-error values
  let result = match_pattern(tm.PError, v.int(42))
  assert result == None
}
