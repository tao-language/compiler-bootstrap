/// Tests for the eval module — Core evaluator.
///
/// These tests verify core evaluator logic only:
/// - Variable lookup via env (utils.list_at)
/// - Beta reduction (explicit parameter application)
/// - Implicit parameter expansion
/// - Neutral term handling
/// - Error path for non-function application
/// - Match evaluation: pattern matching, guards, bindings
/// - FFI integration
///
/// Trivial data-pass-through tests (Typ, Hole, Lit, LitT, Ctr, Rcd,
/// RcdT, Fix, Ann) have been removed — they only verify data flows
/// through, not logic.
import core/eval.{eval, match_pattern}
import core/ffi.{type FFI}
import core/literals as lit
import core/term as tm
import core/value as v
import gleam/option.{None, Some}

// ============================================================================
// Variable lookup — tests utils.list_at logic
// ============================================================================

pub fn eval_var_defined_test() {
  let env = [v.int(42), v.float(3.14)]
  let term = tm.Var(0)
  let result = eval([], env, term)
  assert result == v.int(42)
}

pub fn eval_var_undefined_test() {
  // Accessing index 0 in empty env returns Err
  let term = tm.Var(0)
  let result = eval([], [], term)
  assert result == v.Err
}

// ============================================================================
// Application — tests do_app logic
// ============================================================================

pub fn eval_app_beta_reduction_test() {
  // ($fn(x: $Int) => x) 42 ~> 42
  let fun = tm.Lam(#("x", tm.LitT(lit.IntT)), tm.Var(0))
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.int(42)
}

pub fn eval_app_neutral_test() {
  // ?10 42 ~> ?10 42 (neutral spine)
  let fun = tm.Hole(10)
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.app(v.NHole([], 10), v.int(42))
}

pub fn eval_app_not_a_function_test() {
  // Applying a non-lambda value yields Err
  let fun = tm.Typ(0)
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.Err
}

// ============================================================================
// FFI integration
// ============================================================================

pub fn eval_call_ffi_some_test() {
  let ffi: FFI = [#("f", fn(_) { Some(v.int(42)) })]
  let term = tm.Call("f", tm.int_t, [])
  let result = eval(ffi, [], term)
  assert result == v.int(42)
}

pub fn eval_call_ffi_none_test() {
  // FFI returns None → falls back to neutral call value
  let ffi: FFI = [#("f", fn(_) { None })]
  let term = tm.Call("f", tm.int_t, [])
  let result = eval(ffi, [], term)
  assert result == v.call("f", v.int_t, [])
}

// ============================================================================
// Match evaluation — tests do_match / do_match_case logic
// ============================================================================

pub fn eval_match_first_case_test() {
  let cases = [tm.Case(tm.PLit(lit.Int(42)), None, tm.float(1.0))]
  let term = tm.Match(tm.Lit(lit.Int(42)), cases)
  let result = eval([], [], term)
  assert result == v.float(1.0)
}

pub fn eval_match_second_case_test() {
  let cases = [
    tm.Case(tm.PLit(lit.Int(0)), None, tm.float(1.0)),
    tm.Case(tm.PLit(lit.Int(42)), None, tm.float(2.0)),
  ]
  let term = tm.Match(tm.Lit(lit.Int(42)), cases)
  let result = eval([], [], term)
  assert result == v.float(2.0)
}

pub fn eval_match_no_cases_test() {
  let term = tm.Match(tm.Lit(lit.Int(42)), [])
  let result = eval([], [], term)
  assert result == v.Err
}

// ============================================================================
// Match with bindings — tests DeBruijn/env ordering
// ============================================================================

pub fn eval_match_bindings_test() {
  // $match {x: 10, y: 20} { | {x: a, y: b} => {x: a, y: b} }
  //    a is #1 = 10, b is #0 = 20
  let arg =
    tm.rcd_open(
      [
        #("x", tm.Lit(lit.Int(10))),
        #("y", tm.Lit(lit.Int(20))),
      ],
      None,
    )
  let cases = [
    tm.Case(
      tm.PRcd(
        [
          #("x", tm.PAlias("a", tm.PAny)),
          #("y", tm.PAlias("b", tm.PAny)),
        ],
        None,
      ),
      None,
      tm.rcd_open(
        [
          #("x", tm.Var(1)),
          #("y", tm.Var(0)),
        ],
        None,
      ),
    ),
  ]
  let term = tm.Match(arg, cases)
  let result = eval([], [], term)
  assert result
    == v.rcd_open(
      [
        #("x", v.int(10)),
        #("y", v.int(20)),
      ],
      None,
    )
}

// ============================================================================
// Match with guards — tests do_match_guard logic
// ============================================================================

pub fn eval_match_guard_fail_test() {
  // $match (42) { | x ? x ~ 0 => 1.0 | _ => 2.0 }
  let term =
    tm.Match(tm.Lit(lit.Int(42)), [
      tm.Case(
        tm.PAlias("x", tm.PAny),
        Some(#(tm.Var(0), tm.PLit(lit.Int(0)))),
        tm.float(1.0),
      ),
      tm.Case(tm.PAny, None, tm.float(2.0)),
    ])
  let result = eval([], [], term)
  assert result == v.float(2.0)
}

pub fn eval_match_guard_pass_test() {
  // $match (42) { | x ? x ~ 42 => 1.0 | _ => 2.0 }
  let term =
    tm.Match(tm.Lit(lit.Int(42)), [
      tm.Case(
        tm.PAlias("x", tm.PAny),
        Some(#(tm.Var(0), tm.PLit(lit.Int(42)))),
        tm.float(1.0),
      ),
      tm.Case(tm.PAny, None, tm.float(2.0)),
    ])
  let result = eval([], [], term)
  assert result == v.float(1.0)
}

pub fn eval_match_guard_bindings_test() {
  // $match (10) { | x ? {x: 20, y: 30} ~ {x: a, y: b} => {x: x, y: a, z: b} }
  //    x is #2 = 10, a is #1 = 20, b is #0 = 30
  let cases = [
    tm.Case(
      tm.PAlias("x", tm.PAny),
      Some(#(
        tm.rcd_open(
          [
            #("x", tm.Lit(lit.Int(20))),
            #("y", tm.Lit(lit.Int(30))),
          ],
          None,
        ),
        tm.PRcd(
          [
            #("x", tm.PAlias("a", tm.PAny)),
            #("y", tm.PAlias("b", tm.PAny)),
          ],
          None,
        ),
      )),
      tm.rcd_open(
        [
          #("x", tm.Var(2)),
          #("y", tm.Var(1)),
          #("z", tm.Var(0)),
        ],
        None,
      ),
    ),
  ]
  let term = tm.Match(tm.Lit(lit.Int(10)), cases)
  let result = eval([], [], term)
  assert result
    == v.rcd_open(
      [
        #("x", v.int(10)),
        #("y", v.int(20)),
        #("z", v.int(30)),
      ],
      None,
    )
}

pub fn eval_match_err_test() {
  let term = tm.Err
  let result = eval([], [], term)
  assert result == v.Err
}

// ============================================================================
// match_pattern — tests the pattern matching algorithm
// ============================================================================

pub fn match_pattern_any_matches_test() {
  assert match_pattern(tm.PAny, v.int(42)) == Some([])
}

pub fn match_pattern_any_matches_float_test() {
  // PAny matches any value type
  assert match_pattern(tm.PAny, v.float(3.14)) == Some([])
}

pub fn match_pattern_typ_match_test() {
  assert match_pattern(tm.PTyp(0), v.Typ(0)) == Some([])
}

pub fn match_pattern_typ_mismatch_test() {
  assert match_pattern(tm.PTyp(1), v.Typ(0)) == None
}

pub fn match_pattern_typ_wrong_value_test() {
  assert match_pattern(tm.PTyp(0), v.int(42)) == None
}

pub fn match_pattern_lit_int_match_test() {
  assert match_pattern(tm.PLit(lit.Int(42)), v.int(42)) == Some([])
}

pub fn match_pattern_lit_int_mismatch_test() {
  assert match_pattern(tm.PLit(lit.Int(1)), v.int(42)) == None
}

pub fn match_pattern_lit_float_match_test() {
  assert match_pattern(tm.PLit(lit.Float(3.14)), v.float(3.14)) == Some([])
}

pub fn match_pattern_litt_int_match_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.int_t) == Some([])
}

pub fn match_pattern_litt_int_mismatch_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.float_t) == None
}

pub fn match_pattern_litt_wrong_value_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.int(42)) == None
}

pub fn match_pattern_alias_bind_test() {
  let result = match_pattern(tm.PAlias("x", tm.PAny), v.int(42))
  assert result == Some([v.int(42)])
}

pub fn match_pattern_alias_nested_test() {
  // Each PAlias prepends the value: inner binds it, then outer binds it again
  let result =
    match_pattern(tm.PAlias("outer", tm.PAlias("inner", tm.PAny)), v.int(42))
  assert result == Some([v.int(42), v.int(42)])
}

pub fn match_pattern_alias_fail_test() {
  let result = match_pattern(tm.PAlias("x", tm.PLit(lit.Int(0))), v.int(42))
  assert result == None
}

pub fn match_pattern_ctr_match_test() {
  let result =
    match_pattern(
      tm.PCtr("Some", tm.PAlias("x", tm.PAny)),
      v.Ctr("Some", v.int(42)),
    )
  assert result == Some([v.int(42)])
}

pub fn match_pattern_ctr_tag_mismatch_test() {
  let result = match_pattern(tm.PCtr("None", tm.PAny), v.Ctr("Some", v.int(42)))
  assert result == None
}

pub fn match_pattern_ctr_wrong_value_test() {
  let result = match_pattern(tm.PCtr("Some", tm.PAny), v.int(42))
  assert result == None
}

pub fn match_pattern_ctr_nested_test() {
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(42)))
  let result =
    match_pattern(
      tm.PCtr("Some", inner),
      v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
    )
  assert result == Some([])
}

pub fn match_pattern_ctr_nested_fail_test() {
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(99)))
  let result =
    match_pattern(
      tm.PCtr("Some", inner),
      v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
    )
  assert result == None
}

pub fn match_pattern_rcd_match_test() {
  let result =
    match_pattern(
      tm.prcd([
        #("x", tm.PLit(lit.Int(1))),
        #("y", tm.PAny),
      ]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
      ]),
    )
  assert result == Some([])
}

pub fn match_pattern_rcd_match_strict_test() {
  let result =
    match_pattern(
      tm.prcd_strict([
        #("x", tm.PLit(lit.Int(1))),
        #("y", tm.PAny),
      ]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
      ]),
    )
  assert result == Some([])
}

pub fn match_pattern_rcd_extra_field_test() {
  // Pattern has field not in value
  let result =
    match_pattern(
      tm.prcd([
        #("x", tm.PAny),
        #("y", tm.PAny),
        #("z", tm.PAny),
      ]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
      ]),
    )
  assert result == None
}

pub fn match_pattern_rcd_fewer_fields_test() {
  // Pattern with fewer fields succeeds
  let result =
    match_pattern(
      tm.prcd([#("x", tm.PAny)]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
      ]),
    )
  assert result == Some([])
}

pub fn match_pattern_rcd_fewer_fields_strict_test() {
  // Pattern with fewer fields succeeds
  let result =
    match_pattern(
      tm.prcd_strict([#("x", tm.PAny)]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
      ]),
    )
  assert result == None
}

pub fn match_pattern_rcd_bindings_test() {
  // PRcd with alias bindings — DeBruijn ordering: x(#2), y(#1), z(#0)
  let result =
    match_pattern(
      tm.prcd([
        #("x", tm.PAlias("a", tm.PAny)),
        #("y", tm.PAlias("b", tm.PAny)),
        #("z", tm.PAlias("c", tm.PAny)),
      ]),
      v.rcd([
        #("x", v.int(1)),
        #("y", v.int(2)),
        #("z", v.int(3)),
      ]),
    )
  assert result == Some([v.int(3), v.int(2), v.int(1)])
}

pub fn match_pattern_rcd_wrong_field_name_test() {
  let result =
    match_pattern(tm.prcd([#("x", tm.PAny)]), v.rcd([#("y", v.int(1))]))
  assert result == None
}

pub fn match_pattern_rcd_value_mismatch_test() {
  let result =
    match_pattern(
      tm.prcd([#("x", tm.PLit(lit.Int(99)))]),
      v.rcd([#("x", v.int(42))]),
    )
  assert result == None
}

pub fn match_pattern_error_match_test() {
  assert match_pattern(tm.PErr, v.Err) == Some([])
}

pub fn match_pattern_error_wrong_value_test() {
  assert match_pattern(tm.PErr, v.int(42)) == None
}
