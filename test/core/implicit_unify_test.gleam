/// Core-level tests pinning sound hole re-anchoring behavior (see
/// docs/implicit-args.md).
///
/// A hole solution's `NVar` levels are relative to the frame the solution
/// was produced in. When the hole's captured env is that same frame,
/// re-anchoring must yield the entry the level named.
import core/ffi
import core/unwrap.{unwrap}
import core/value as v

// ============================================================================
// Re-anchoring across frames (unwrap)
// ============================================================================

/// When the hole's captured env is the same frame the solution's levels
/// address, re-anchoring proceeds and yields the entry the level named
/// (var(0) = outermost = int(1)).
pub fn reanchor_aligned_frame_resolves_test() {
  let subst = [#(1, #([v.int(2), v.int(1)], v.var(0)))]
  let hole = v.hole([v.int(2), v.int(1)], 1)
  assert unwrap([], subst, hole) == v.int(1)
}
