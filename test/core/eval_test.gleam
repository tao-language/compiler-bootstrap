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
import core/eval.{do_app, do_match, eval, match_pattern, MatchAccept, MatchNeutral, MatchReject}
import core/ffi.{build, type FFI}
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
  let fun = tm.Hole(Some(10))
  let term = tm.App(fun, tm.Lit(lit.Int(42)))
  let result = eval([], [], term)
  assert result == v.app(v.NHole([], Some(10)), v.int(42))
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
  let term = tm.Call("f", tm.int_t, tm.Rcd([], None))
  let result = eval(ffi, [], term)
  assert result == v.int(42)
}

pub fn eval_call_ffi_none_test() {
  // FFI returns None → falls back to neutral call value
  let ffi: FFI = [#("f", fn(_) { None })]
  let term = tm.Call("f", tm.int_t, tm.Rcd([], None))
  let result = eval(ffi, [], term)
  assert result == v.call("f", v.int_t, v.Rcd([], None))
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

pub fn eval_match_partial_rcd_scrutinee_deferred_test() {
  // A match on a constructed record whose fields are still neutral must
  // not bake in the wrong case: a structural pattern cannot rule out a
  // neutral field, so the match is kept neutral (`NMatch`) and is
  // re-reduced once the scrutinee becomes fully concrete. This is what
  // makes Tao tuple matches (`match a, b { | ... }` → a record match
  // over `{1: a, 2: b}`) reduce correctly for both True/True inputs.
  let env = [v.var(0), v.var(1)]
  let arg = tm.rcd_open([#("1", tm.Var(0)), #("2", tm.Var(1))], None)
  let cases = [
    tm.Case(
      tm.prcd_strict([
        #("1", tm.PCtr("True", tm.prcd_strict([]))),
        #("2", tm.PCtr("True", tm.prcd_strict([]))),
      ]),
      None,
      tm.Lit(lit.Int(1)),
    ),
    tm.Case(
      tm.prcd_strict([#("1", tm.PAny), #("2", tm.PAny)]),
      None,
      tm.Lit(lit.Int(2)),
    ),
  ]
  let result = eval([], env, tm.Match(arg, cases))
  let expected_scrutinee =
    v.Rcd(
      [#("1", #(v.Neut(v.NVar(0)), None)), #("2", #(v.Neut(v.NVar(1)), None))],
      None,
    )
  assert result == v.Neut(v.NMatch(env, expected_scrutinee, cases))
  // Fully concrete scrutinees select their case as before.
  let t = v.Ctr("True", v.Rcd([], None))
  let f = v.Ctr("False", v.Rcd([], None))
  let both_true = v.Rcd([#("1", #(t, None)), #("2", #(t, None))], None)
  assert do_match(build, env, both_true, cases) == v.Lit(lit.Int(1))
  let true_false = v.Rcd([#("1", #(t, None)), #("2", #(f, None))], None)
  assert do_match(build, env, true_false, cases) == v.Lit(lit.Int(2))
}

pub fn eval_match_partial_rcd_binding_patterns_eager_test() {
  // Patterns that only bind (variables, open tails) are decidable even
  // against a partially concrete scrutinee — the value's shape is known
  // — so the match reduces eagerly. This is how `.` field access
  // (a single-case open-tail record pattern) works on module records
  // whose entries are still declaration holes.
  let env = [v.var(0), v.var(1)]
  let arg_val = v.Rcd([#("fun", #(v.Neut(v.NVar(0)), None))], None)
  let cases = [
    tm.Case(
      tm.PRcd([#("fun", tm.pvar("fun"))], Some(tm.PAny)),
      None,
      tm.Var(0),
    ),
  ]
  let result = do_match(build, env, arg_val, cases)
  assert result == v.Neut(v.NVar(0))
}

pub fn eval_match_neutral_tail_deferred_test() {
  // A record whose *tail* is neutral: a field not found in the head is
  // searched for in the tail, and the outcome depends on what the tail
  // resolves to — so the match stays neutral instead of falling through
  // to a later case (which would bake in the wrong branch).
  let env = [v.var(0)]
  let arg_val = v.Rcd([], Some(v.Neut(v.NVar(0)))) // `{..r}`
  let cases = [
    tm.Case(
      tm.PRcd([#("y", tm.pvar("yy"))], Some(tm.PAny)),
      None,
      tm.Var(0),
    ),
    tm.Case(tm.PAny, None, tm.Lit(lit.Int(0))),
  ]
  let result = do_match(build, env, arg_val, cases)
  assert result == v.Neut(v.NMatch(env, arg_val, cases))
}

pub fn eval_match_neutral_tail_field_in_head_eager_test() {
  // A field found in the head is decidable even when the tail is
  // neutral: the lookup never reaches the tail, so the match reduces
  // eagerly.
  let env = [v.var(0)]
  let arg_val =
    v.Rcd([#("x", #(v.int(1), None))], Some(v.Neut(v.NVar(0))))
  let cases = [
    tm.Case(
      tm.PRcd([#("x", tm.pvar("x"))], Some(tm.PAny)),
      None,
      tm.Var(0),
    ),
  ]
  let result = do_match(build, env, arg_val, cases)
  assert result == v.int(1)
}

pub fn eval_match_neutral_scrutinee_lit_deferred_test() {
  // A literal pattern cannot be decided against a neutral scrutinee:
  // the catch-all below it must not win yet.
  let env = []
  let scrut = v.hole(env, 0)
  let cases = [
    tm.Case(tm.pint(1), None, tm.int(10)),
    tm.Case(tm.PAny, None, tm.int(20)),
  ]
  let result = do_match(build, env, scrut, cases)
  assert result == v.match(env, scrut, cases)
}

pub fn eval_match_neutral_scrutinee_pany_eager_test() {
  // A case that only binds is decidable against any value, neutral
  // included: it cannot fail, so the match reduces immediately.
  let env = [v.var(0)]
  let scrut = v.Neut(v.NVar(0))
  let cases = [tm.Case(tm.PAny, None, tm.Var(0))]
  let result = do_match(build, env, scrut, cases)
  assert result == scrut
}

pub fn eval_match_ctr_tag_neutral_arg_eager_test() {
  // A constructor's tag is decidable even when its argument record is
  // still neutral: the matching tag accepts (binding the neutral),
  // and a mismatched tag rejects down to the next case.
  let env = [v.var(0)]
  let arg = v.Rcd([#("1", #(v.Neut(v.NVar(0)), None))], None)
  let some_neut = v.Ctr("Some", arg)
  let accept_tag = [
    tm.Case(tm.PCtr("Some", tm.pvar("x")), None, tm.Var(0)),
    tm.Case(tm.PAny, None, tm.int(0)),
  ]
  // The binding is the whole argument record (neutral and all).
  assert do_match(build, env, some_neut, accept_tag) == arg
  let reject_tag = [
    tm.Case(tm.PCtr("None", tm.pvar("x")), None, tm.Var(0)),
    tm.Case(tm.PAny, None, tm.int(0)),
  ]
  assert do_match(build, env, some_neut, reject_tag) == v.int(0)
}

pub fn eval_match_guard_neutral_deferred_test() {
  // A guard whose value is still neutral keeps the case undecided — it
  // must not be treated as a failed case falling through to the next.
  let env = [v.var(0)]
  let arg_val = v.Rcd([#("x", #(v.int(1), None))], None)
  let cases = [
    tm.Case(
      tm.PRcd([#("x", tm.pint(1))], Some(tm.PAny)),
      Some(#(tm.Var(0), tm.PCtr("True", tm.prcd_strict([])))),
      tm.int(10),
    ),
    tm.Case(tm.PAny, None, tm.int(20)),
  ]
  let result = do_match(build, env, arg_val, cases)
  assert result == v.Neut(v.NMatch(env, arg_val, cases))
  // A concrete guard is decided: True keeps the guarded case, False
  // falls through.
  let true_ = v.Ctr("True", v.Rcd([], None))
  let false_ = v.Ctr("False", v.Rcd([], None))
  assert do_match(build, [true_], arg_val, cases) == v.int(10)
  assert do_match(build, [false_], arg_val, cases) == v.int(20)
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
  assert match_pattern(tm.PAny, v.int(42)) == MatchAccept([])
}

pub fn match_pattern_any_matches_float_test() {
  // PAny matches any value type
  assert match_pattern(tm.PAny, v.float(3.14)) == MatchAccept([])
}

pub fn match_pattern_typ_match_test() {
  assert match_pattern(tm.PTyp(0), v.Typ(0)) == MatchAccept([])
}

pub fn match_pattern_typ_mismatch_test() {
  assert match_pattern(tm.PTyp(1), v.Typ(0)) == MatchReject
}

pub fn match_pattern_typ_wrong_value_test() {
  assert match_pattern(tm.PTyp(0), v.int(42)) == MatchReject
}

pub fn match_pattern_lit_int_match_test() {
  assert match_pattern(tm.PLit(lit.Int(42)), v.int(42)) == MatchAccept([])
}

pub fn match_pattern_lit_int_mismatch_test() {
  assert match_pattern(tm.PLit(lit.Int(1)), v.int(42)) == MatchReject
}

pub fn match_pattern_lit_float_match_test() {
  assert match_pattern(tm.PLit(lit.Float(3.14)), v.float(3.14)) == MatchAccept([])
}

pub fn match_pattern_litt_int_match_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.int_t) == MatchAccept([])
}

pub fn match_pattern_litt_int_mismatch_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.float_t) == MatchReject
}

pub fn match_pattern_litt_wrong_value_test() {
  assert match_pattern(tm.PLitT(lit.IntT), v.int(42)) == MatchReject
}

pub fn match_pattern_alias_bind_test() {
  let result = match_pattern(tm.PAlias("x", tm.PAny), v.int(42))
  assert result == MatchAccept([v.int(42)])
}

pub fn match_pattern_alias_nested_test() {
  // Each PAlias prepends the value: inner binds it, then outer binds it again
  let result =
    match_pattern(tm.PAlias("outer", tm.PAlias("inner", tm.PAny)), v.int(42))
  assert result == MatchAccept([v.int(42), v.int(42)])
}

pub fn match_pattern_alias_fail_test() {
  let result = match_pattern(tm.PAlias("x", tm.PLit(lit.Int(0))), v.int(42))
  assert result == MatchReject
}

pub fn match_pattern_ctr_match_test() {
  let result =
    match_pattern(
      tm.PCtr("Some", tm.PAlias("x", tm.PAny)),
      v.Ctr("Some", v.int(42)),
    )
  assert result == MatchAccept([v.int(42)])
}

pub fn match_pattern_ctr_tag_mismatch_test() {
  let result = match_pattern(tm.PCtr("None", tm.PAny), v.Ctr("Some", v.int(42)))
  assert result == MatchReject
}

pub fn match_pattern_ctr_wrong_value_test() {
  let result = match_pattern(tm.PCtr("Some", tm.PAny), v.int(42))
  assert result == MatchReject
}

pub fn match_pattern_ctr_nested_test() {
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(42)))
  let result =
    match_pattern(
      tm.PCtr("Some", inner),
      v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
    )
  assert result == MatchAccept([])
}

pub fn match_pattern_ctr_nested_fail_test() {
  let inner = tm.PCtr("Int", tm.PLit(lit.Int(99)))
  let result =
    match_pattern(
      tm.PCtr("Some", inner),
      v.Ctr("Some", v.Ctr("Int", v.Lit(lit.Int(42)))),
    )
  assert result == MatchReject
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
  assert result == MatchAccept([])
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
  assert result == MatchAccept([])
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
  assert result == MatchReject
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
  assert result == MatchAccept([])
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
  assert result == MatchReject
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
  assert result == MatchAccept([v.int(3), v.int(2), v.int(1)])
}

pub fn match_pattern_rcd_wrong_field_name_test() {
  let result =
    match_pattern(tm.prcd([#("x", tm.PAny)]), v.rcd([#("y", v.int(1))]))
  assert result == MatchReject
}

pub fn match_pattern_rcd_value_mismatch_test() {
  let result =
    match_pattern(
      tm.prcd([#("x", tm.PLit(lit.Int(99)))]),
      v.rcd([#("x", v.int(42))]),
    )
  assert result == MatchReject
}

pub fn match_pattern_error_match_test() {
  assert match_pattern(tm.PErr, v.Err) == MatchAccept([])
}

pub fn match_pattern_error_wrong_value_test() {
  assert match_pattern(tm.PErr, v.int(42)) == MatchReject
}

// ---- Three-valued matching against neutrals ----

pub fn match_pattern_neutral_value_test() {
  // Structural patterns cannot be decided against a neutral value: it
  // may resolve to a matching value.
  let neut = v.Neut(v.NVar(0))
  assert match_pattern(tm.PLit(lit.Int(1)), neut) == MatchNeutral
  assert match_pattern(tm.PLitT(lit.IntT), neut) == MatchNeutral
  assert match_pattern(tm.PTyp(0), neut) == MatchNeutral
  assert match_pattern(tm.PCtr("Some", tm.PAny), neut) == MatchNeutral
  assert match_pattern(tm.prcd([#("x", tm.PAny)]), neut) == MatchNeutral
  assert match_pattern(tm.PErr, neut) == MatchNeutral
  // Binding patterns match anything, neutral included.
  assert match_pattern(tm.PAny, neut) == MatchAccept([])
  assert match_pattern(tm.pvar("x"), neut) == MatchAccept([neut])
}

pub fn match_pattern_ctr_tag_decidable_test() {
  // The tag is decidable: equal tags recurse into the (neutral)
  // argument and accept, mismatched tags reject.
  let neut = v.Neut(v.NVar(0))
  let arg = v.Rcd([#("1", #(neut, None))], None)
  let some = v.Ctr("Some", arg)
  // The tag decides; the binding is the whole argument record.
  assert match_pattern(tm.PCtr("Some", tm.pvar("x")), some) == MatchAccept([arg])
  assert match_pattern(tm.PCtr("None", tm.PAny), some) == MatchReject
}

pub fn match_pattern_rcd_neutral_tail_test() {
  // A field not in the head is searched for in the tail: a neutral
  // tail keeps the lookup undecided, a missing tail rejects, and a
  // field found in the head never reaches the tail.
  let neut = v.Neut(v.NVar(0))
  assert match_pattern(tm.prcd([#("y", tm.PAny)]), v.Rcd([], Some(neut)))
    == MatchNeutral
  assert match_pattern(tm.prcd([#("y", tm.PAny)]), v.Rcd([], None))
    == MatchReject
  let head_and_tail = v.Rcd([#("x", #(v.int(1), None))], Some(neut))
  assert match_pattern(tm.prcd([#("x", tm.PAny)]), head_and_tail)
    == MatchAccept([])
}

pub fn match_pattern_rcd_neutral_field_test() {
  // A field found in the head is matched with its pattern: a literal
  // cannot be decided against a neutral field, a binding accepts it.
  let neut = v.Neut(v.NVar(0))
  let value = v.Rcd([#("x", #(neut, None))], None)
  assert match_pattern(tm.prcd([#("x", tm.PLit(lit.Int(1)))]), value)
    == MatchNeutral
  assert match_pattern(tm.prcd([#("x", tm.pvar("x"))]), value)
    == MatchAccept([neut])
}

// ============================================================================
// For / Fix / Ann / TypeDef evaluation
// ============================================================================

/// `For` beta-reduces exactly like `Lam` at the value level: applying a
/// value to a For consumes the quantifier's argument slot and returns
/// the body with that slot bound. (This is why an implicit argument eats
/// one application when the function is applied directly at the value
/// level — the type argument is a value-level slot in NbE.)
pub fn eval_for_beta_reduction_test() {
  let for_ = v.For([], #("a", v.Typ(0)), tm.Var(0))
  assert eval([], [], tm.App(tm.For(#("a", tm.Typ(0)), tm.Var(0)), tm.int_t))
    == v.int_t
  // The quantified slot is bound to the applied value: the body `a` of
  // `for<a>. a` reduces to the argument.
  assert do_app([], for_, v.int(7)) == v.int(7)
}

/// `Fix` feeds itself as its own binding: `fix f. fn(x) => x` applied to
/// `5` evaluates the body with `f` (the fixpoint) in the environment and
/// returns the body's result.
pub fn eval_fix_self_application_test() {
  let fix_ = v.Fix([], "f", tm.Lam(#("x", tm.int_t), tm.Var(0)))
  assert do_app([], fix_, v.int(5)) == v.int(5)
}

/// `Ann` is transparent to evaluation: the annotation is dropped.
pub fn eval_ann_test() {
  assert eval([], [], tm.Ann(tm.int(1), tm.int_t)) == v.int(1)
}

/// A type definition evaluates to the corresponding `TypeDef` value with
/// the parameter types evaluated and the variant terms kept as terms.
pub fn eval_type_def_test() {
  let param = #("a", tm.Typ(0))
  let variant = #("C", tm.Variant([], tm.Var(0), tm.ctr("T", [])))
  let td = tm.TypeDefinition(params: [param], arg: tm.Var(0), variants: [variant])
  let expected =
    v.TypeDef(
      [],
      v.TypeDefinition(
        params: [#("a", v.Typ(0))],
        arg: tm.Var(0),
        variants: [#("C", v.Variant([], tm.Var(0), tm.ctr("T", [])))],
      ),
    )
  assert eval([], [], tm.TypeDef(td)) == expected
}

/// Record field defaults are evaluated like field values: both the value
/// and its default survive evaluation.
pub fn eval_rcd_field_default_test() {
  let field = #("a", #(tm.int(1), Some(tm.int(42))))
  let term = tm.Rcd([field], None)
  let expected = v.Rcd([#("a", #(v.int(1), Some(v.int(42))))], None)
  assert eval([], [], term) == expected
}
