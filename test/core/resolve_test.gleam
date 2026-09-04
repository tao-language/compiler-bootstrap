/// Tests for the `resolve` module — final hole resolution after
/// type checking, including termination on self-referential (cyclic)
/// hole solutions.
import core/context.{Context, new_ctx}
import core/error as e
import core/ffi
import core/resolve
import core/term as tm
import core/value as v
import gleam/option.{None, Some}
import syntax/span

const s1 = span.Span("", 1, 1, 1, 1)

const s2 = span.Span("", 2, 2, 2, 2)

/// 1. A value-level cycle terminates: the hole's solution is a record
/// that contains the hole itself. Resolution stops at the self-reference
/// and leaves it as the (unsolvable) hole instead of looping.
pub fn resolve_value_cycle_terminates_test() {
  let ffi = ffi.build
  let hole_ = v.hole([], 0)
  let subst = [#(0, v.rcd([#("a", hole_)]))]
  assert resolve.value(ffi, subst, hole_) == v.rcd([#("a", hole_)])
}

/// 2. A term-level cycle terminates: the hole's solution is a lambda
/// whose body is the hole itself. The cycle guard leaves the body as the
/// hole rather than inlining it forever.
pub fn resolve_term_cycle_terminates_test() {
  let ffi = ffi.build
  let subst = [#(0, v.Lam([], #("x", v.int_t), tm.Hole(Some(0))))]
  assert resolve.term(ffi, subst, [], tm.Hole(Some(0)))
    == tm.Lam(#("x", tm.int_t), tm.Hole(Some(0)))
}

/// 3. `resolve.context` finalizes the whole context with the same
/// substitution: holes in the environment, in the type bindings, and in
/// the values carried by accumulated errors all resolve to their
/// solutions (unsolved holes stay holes).
pub fn resolve_context_finalizes_env_types_errors_test() {
  let ffi = ffi.build
  let ctx0 =
    Context(
      ..new_ctx,
      ffi: ffi,
      // The module record's `x` value is an unsolved hole...
      env: [v.rcd([#("x", v.hole([], 0))])],
      // ...and its type is another one.
      types: [#("m", v.rcd([#("x", v.hole([], 1))]))],
      subst: [#(0, v.int(42)), #(1, v.int_t)],
      // The error carries one solved hole (0) and one never-solved one (2).
      errors: [
        e.Error(
          e.TypeMismatch(#(v.hole([], 0), s1), #(v.hole([], 2), s2)),
          s1,
          [],
        ),
      ],
    )
  let ctx = resolve.context(ctx0)
  assert ctx.env == [v.rcd([#("x", v.int(42))])]
  assert ctx.types == [#("m", v.rcd([#("x", v.int_t)]))]
  assert ctx.errors
    == [
      e.Error(
        e.TypeMismatch(#(v.int(42), s1), #(v.hole([], 2), s2)),
        s1,
        [],
      ),
    ]
}

/// 4. The plain positive path for terms: a solved hole is replaced by its
/// quoted solution; unsolved holes (with or without an ID) are untouched.
pub fn resolve_term_hole_with_concrete_solution_test() {
  let ffi = ffi.build
  assert resolve.term(ffi, [#(0, v.int_t)], [], tm.Hole(Some(0))) == tm.int_t
  assert resolve.term(ffi, [], [], tm.Hole(Some(5))) == tm.Hole(Some(5))
  assert resolve.term(ffi, [], [], tm.Hole(None)) == tm.Hole(None)
}
