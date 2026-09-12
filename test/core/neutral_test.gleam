/// Tests for the core semantic invariant of neutrals:
///
///   a neutral value is a *deferred* computation — as soon as the hole it
///   depends on is solved, re-evaluating the neutral yields the fully
///   reduced final value.
///
/// Top-level neutrals reduce directly through `unwrap`. Neutrals nested
/// inside records/constructors or inside FFI-call arguments reduce through
/// the pipeline used to display and evaluate values: quote the value to a
/// term, resolve every hole in the term (`resolve.term`), and re-evaluate.
/// (`unwrap` alone is intentionally non-recursive into value constructors,
/// so it cannot reach those.)
import core/context.{type Subst}
import core/eval.{eval}
import core/ffi
import core/quote.{quote}
import core/resolve
import core/term as tm
import core/unwrap.{unwrap}
import core/value.{type Env, type Value} as v
import gleam/option.{None, Some}

/// The value-reduction pipeline: quote → resolve holes → re-evaluate.
fn reduce(ffi: ffi.FFI, subst: Subst, env: Env, value: Value) -> Value {
  value
  |> quote(ffi, env, _)
  |> resolve.term(ffi, subst, env, _)
  |> eval(ffi, env, _)
}

/// 1. A neutral application keeps the neutral until the hole is solved,
/// then β-reduces to the argument.
pub fn neutral_app_reduces_after_solve_test() {
  let ffi = ffi.build
  // `?0(1)`: the head is not yet a lambda, so the app stays neutral.
  let n = eval(ffi, [], tm.App(tm.Hole(Some(0)), tm.int(1)))
  assert n == v.Neut(v.NApp(v.NHole([], Some(0)), v.int(1)))
  // Unsolved: still neutral.
  assert unwrap(ffi, [], n) == n
  // Solving `?0` to the identity lambda reduces the whole app to `1`.
  let subst = [#(0, #([], v.Lam([], #("x", v.int_t), tm.Var(0))))]
  assert unwrap(ffi, subst, n) == v.int(1)
}

/// 2. A neutral match selects its case *after* the scrutinee hole is
/// solved, and the selected body runs with its pattern binding.
pub fn neutral_match_reduces_after_solve_test() {
  let ffi = ffi.build
  let cases = [
    tm.Case(tm.pint(1), None, tm.int(10)),
    tm.Case(tm.pvar("x"), None, tm.Var(0)),
  ]
  let n = eval(ffi, [], tm.Match(tm.Hole(Some(0)), cases))
  assert n == v.Neut(v.NMatch([], v.Neut(v.NHole([], Some(0))), cases))
  // Scrutinee 2: the catch-all case is picked post-solve, with the
  // binding — the match does not reduce eagerly.
  assert unwrap(ffi, [#(0, #([], v.int(2)))], n) == v.int(2)
  // Scrutinee 1: the literal case is picked instead.
  assert unwrap(ffi, [#(0, #([], v.int(1)))], n) == v.int(10)
}

/// 3. A neutral nested inside a value constructor (record or ctor) is
/// reduced once its hole is solved, through the quote → resolve → eval
/// pipeline.
pub fn neutral_nested_in_record_reduces_test() {
  let ffi = ffi.build
  let subst = [#(0, #([], v.Lam([], #("x", v.int_t), tm.Var(0))))]
  let app_neutral = v.Neut(v.NApp(v.NHole([], Some(0)), v.int(1)))
  // Record field.
  assert reduce(ffi, subst, [], v.rcd([#("f", app_neutral)]))
    == v.rcd([#("f", v.int(1))])
  // Constructor argument record.
  assert reduce(ffi, subst, [], v.ctr("C", [#("f", app_neutral)]))
    == v.ctr("C", [#("f", v.int(1))])
}

/// 4. A call to a *defined* builtin with an unknown argument is deferred
/// as a neutral `NCall`, and reduces to the builtin's result once the
/// argument hole is solved.
pub fn neutral_ffi_call_reduces_after_solve_test() {
  let ffi = ffi.build
  // `int_add(?0, 1)`: the argument is not concrete, so the call is
  // deferred rather than erroring.
  let n =
    eval(
      ffi,
      [],
      tm.Call(
        "int_add",
        tm.int_t,
        tm.rcd([#("", tm.Hole(Some(0))), #("", tm.int(1))]),
      ),
    )
  assert n
    == v.Neut(v.NCall(
      "int_add",
      v.int_t,
      v.rcd([#("", v.hole([], 0)), #("", v.int(1))]),
    ))
  // Unsolved: still neutral...
  assert reduce(ffi, [], [], n) == n
  // ...solved: the builtin reduces.
  assert reduce(ffi, [#(0, #([], v.int(1)))], [], n) == v.int(2)
}

/// 5. A match deferred on a *partially concrete* scrutinee (a record
/// whose fields are still holes) re-reduces once the holes are solved.
/// `unwrap` alone keeps it neutral — it is not recursive into value
/// constructors — and the quote → resolve → re-evaluate pipeline
/// completes the reduction.
pub fn neutral_match_partial_rcd_reduces_test() {
  let ffi = ffi.build
  let env = []
  let cases = [
    tm.Case(
      tm.prcd_strict([
        #("1", tm.PCtr("True", tm.prcd_strict([]))),
        #("2", tm.PCtr("True", tm.prcd_strict([]))),
      ]),
      None,
      tm.int(1),
    ),
    tm.Case(
      tm.prcd_strict([#("1", tm.PAny), #("2", tm.PAny)]),
      None,
      tm.int(2),
    ),
  ]
  let scrutinee =
    v.Rcd(
      [#("1", #(v.hole(env, 0), None)), #("2", #(v.hole(env, 1), None))],
      None,
    )
  let n = v.match(env, scrutinee, cases)
  // `unwrap` alone keeps it neutral: it does not reach into the
  // record's fields, so nothing is lost and nothing loops.
  assert unwrap(ffi, [], n) == n
  let t = v.ctr("True", [])
  let f = v.ctr("False", [])
  // Once the holes are solved, the pipeline reduces the match: the
  // catch-all picks True/False...
  assert reduce(ffi, [#(0, #([], t)), #(1, #([], f))], env, n) == v.int(2)
  // ...and the first case picks True/True.
  assert reduce(ffi, [#(0, #([], t)), #(1, #([], t))], env, n) == v.int(1)
}

/// 6. A neutral match whose blocker is a variable (never solved by
/// `unwrap`) stays neutral and stable: re-unwrapping it must terminate
/// and return it unchanged, not loop or force a decision.
pub fn neutral_match_undecided_stays_neutral_test() {
  let ffi = ffi.build
  let env = [v.var(0)]
  let arg_val = v.Rcd([#("1", #(v.Neut(v.NVar(0)), None))], None)
  let cases = [
    tm.Case(
      tm.prcd_strict([#("1", tm.PCtr("True", tm.prcd_strict([])))]),
      None,
      tm.int(1),
    ),
    tm.Case(tm.PAny, None, tm.int(2)),
  ]
  let n = v.Neut(v.NMatch(env, arg_val, cases))
  // No solution for the blocker: the match is kept, unchanged.
  assert unwrap(ffi, [], n) == n
  // An unrelated solved hole does not change the outcome either.
  assert unwrap(ffi, [#(0, #([], v.int(7)))], n) == n
}
