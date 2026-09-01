/// Tests for the de Bruijn level/index invariants of `Value`/`Term`.
///
/// Values refer to environment entries by *level* (the size of the
/// environment when the entry was pushed; unchanged by later push/pop),
/// terms by *index* (0 = innermost). `quote` converts levels to indices
/// with `index = env_size - level - 1` — the conversion is *not* the
/// identity. These tests pin that convention: if the level scheme is ever
/// "simplified" to plain index counting, they must fail.
import core/eval.{eval}
import core/ffi
import core/quote.{quote}
import core/term as tm
import core/value as v
import gleam/list
import gleam/option.{None}

/// 1. Quoting converts a level to an index, not the identity: in an
/// environment of size 2 the level-1 entry is the innermost (index 0) and
/// the level-0 entry is the outermost (index 1).
pub fn quote_nvar_index_conversion_test() {
  let ffi = ffi.build
  // env of size 2, innermost first: [var(1), var(0)]
  let env = v.env_push([], 2)
  assert env == [v.var(1), v.var(0)]
  assert quote(ffi, 2, v.var(1)) == tm.Var(0)
  assert quote(ffi, 2, v.var(0)) == tm.Var(1)
}

/// 2. A level keeps naming the same entry across push/pop: the value
/// `var(0)` captured *inside* a larger environment still quotes to the
/// index of the outermost entry, and re-evaluating in a *different*
/// environment with the same levels gives the same value back.
pub fn quote_level_stable_across_push_pop_test() {
  let ffi = ffi.build
  let env0 = v.env_push([], 1) // [var(0)] = `a`
  // `x` pushed over `a` (x in scope when `a`'s reference is captured)
  let _env1 = v.env_push(env0, 1)
  let v_a = v.var(0)
  // `x` popped, `y` pushed: same levels, different entry
  let env2 = v.env_push(env0, 1)
  // `a` must be addressed at index 1 (the outermost entry), not at 0
  // (which would bind to `y` — the entry that merely sits innermost).
  assert quote(ffi, 2, v_a) == tm.Var(1)
  // Round-trip: re-evaluating that index in env2 gives `a` back.
  assert eval(ffi, env2, tm.Var(1)) == v_a
}

/// 3. The normalization law: for a value built in `env`,
/// `eval(env, quote(env, v)) == v` — for variables at every level, records,
/// constructors, holes, neutral applications, deferred calls, neutral
/// matches, and captured lambda/Pi bodies. A single regression here breaks
/// every later phase of the compiler.
pub fn eval_quote_round_trip_test() {
  let ffi = ffi.build
  // Every entry of `env` is a var with its own level, so evaluating a
  // quoted index hands the same value back.
  let env = v.env_push([], 3) // [var(2), var(1), var(0)]
  let size = list.length(env)
  let values = [
    v.var(0),
    v.var(1),
    v.var(2),
    v.rcd([#("f", v.var(1)),]),
    v.ctr("C", [#("x", v.var(0)),]),
    v.hole(env, 7),
    // Neutral application: head not yet a lambda.
    v.Neut(v.NApp(v.NVar(1), v.int(5))),
    // Deferred call to an undefined name (no FFI entry).
    v.call("ext", v.int_t, v.int(1)),
    // Neutral match: scrutinee not yet concrete.
    v.match(env, v.NVar(0), [tm.Case(tm.PAny, None, tm.Var(0))]),
    // Captured bodies: the parameter slot is level `size`, the body's
    // Var(0) names it.
    v.Lam(env, #("x", v.int_t), tm.Var(0)),
    v.Pi(env, #("a", v.int_t), tm.Var(0)),
  ]
  assert list.all(values, fn(value) {
    eval(ffi, env, quote(ffi, size, value)) == value
  })
}
