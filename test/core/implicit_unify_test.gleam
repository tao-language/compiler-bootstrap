/// Core-level tests pinning sound hole-unwrap behavior (see
/// docs/implicit-args.md).
///
/// A hole solution is used in the frame it was produced in: its `NVar`
/// levels and its captured `For`/`Lam`/`Pi`/`Fix` bodies address the
/// global frame, so `unwrap` returns the solution as-is (sub-holes
/// re-unwrapped, nothing re-anchored).
import core/unwrap.{unwrap}
import core/value as v

// ============================================================================
// Unwrap keeps the solution's own frame
// ============================================================================

/// `unwrap` returns the solution as-is: the solution's `NVar` levels
/// already address the global frame (the same frame every other value in
/// the context addresses), so no re-anchoring is needed. (The old
/// `normalize_value` round-trip re-expressed the solution against the
/// solve env, which re-captured its `For`/`Lam`/`Pi`/`Fix` bodies under
/// that env and silently re-bound their `Var`s to the solve env's slots —
/// module records — the corruption behind the result.tao hang, T4.)
pub fn unwrap_keeps_solution_frame_test() {
  let subst = [#(1, #([v.int(2), v.int(1)], v.var(0)))]
  let hole = v.hole([v.int(2), v.int(1)], 1)
  assert unwrap([], subst, hole) == v.var(0)
}
