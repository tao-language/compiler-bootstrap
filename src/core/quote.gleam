/// Quote — Convert Values back to Terms
///
/// The `quote` module reifies evaluated values (De Bruijn levels) back into
/// syntax terms (De Bruijn indices). This is used for:
/// - Displaying inferred types as readable terms
/// - Normalization by evaluation results
/// - Error message generation
///
/// ## How Quoting Works
///
/// Values use De Bruijn levels where `HVar(0)` is the innermost binder.
/// Terms use De Bruijn indices where `Var(0)` is the innermost binder.
///
/// When quoting a value, we need to know the number of binders above the
/// value's scope to convert levels to indices correctly.
///
/// ## The Key Invariant: Quote Does NOT Evaluate
///
/// Quote transforms a `Value` back to a `Term` by re-wrapping lambdas.
/// It never calls `eval`. This is critical — if `quote` calls `eval`,
/// you get exponential blowup in runtime.
///
/// ## Example
///
/// ```gleam
/// // Identity function: VLam(("x", unit), Var(0))
/// let v = VLam(#("x", VRcd([])), Var(0, empty))
/// let term = quote(v)
/// // term == Lam(#("x", Rcd([])), Var(0, empty), empty)
/// ```

import core/ast.{type Term, type Value}
import core/subst.{force_levels_to_indices}

/// Quote a top-level value to a term.
///
/// This is the main entry point for quoting. It assumes the value is at
/// the top level (no enclosing binders) and converts all De Bruijn levels
/// to indices accordingly.
///
/// For quoting a value at a specific De Bruijn offset, use `quote_at` instead.
///
/// ## Example
///
/// ```gleam
/// import core/quote.{quote}
/// import core/ast.{VLam, VLit, LitInt, Rcd, Var}
///
/// let v = VLam(#("x", VRcd([])), Var(0, empty))
/// let t = quote(v)
/// // t == Lam(#("x", Rcd([])), Var(0, empty), empty)
/// ```
pub fn quote(value: Value) -> Term {
  force_levels_to_indices(value, 0)
}

/// Quote a value at a specific De Bruijn offset.
///
/// Use this when the value was evaluated inside `level` enclosing binders.
/// The `level` parameter tells the quote function how many De Bruijn binders
/// sit above the value's scope.
///
/// ## Example
///
/// ```gleam
/// // Quoting a lambda body where `x` is at level 0 inside a binder
/// // with 2 outer binders means: Var(1) (skip 1 for the current lambda, 1 for outer)
/// let term = quote_at(value, 2)
/// ```
pub fn quote_at(value: Value, level: Int) -> Term {
  force_levels_to_indices(value, level)
}
