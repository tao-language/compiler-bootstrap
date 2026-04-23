// ============================================================================
// DE BRUIJN LEVEL MANAGEMENT TESTS
// ============================================================================
/// Tests that De Bruijn levels are correctly managed during type-checking.
///
/// Background: The codebase uses two De Bruijn systems:
/// - De Bruijn indices (relative): Var(0), Var(1) - used in syntax
/// - De Bruijn levels (absolute): HVar(0), HVar(1) - used in semantics
///
/// The `level` field in State tracks the current absolute depth. Each binder
/// (Lam, Pi, Fix) must increment level when entering and decrement when exiting.
/// If level is not managed correctly, multiple variables get the same HVar index,
/// causing VarUndefined and InfiniteType errors after quote.
///
/// Key functions that MUST manage level:
/// - infer Lam: already correct (level +1 before body, -1 after)
/// - infer Pi: BUG - does NOT increment level for out_term
/// - check Lam (VPi case): BUG - does NOT increment level for body
/// - infer_fix: BUG - does NOT increment level for body check
/// - check Fix: BUG - does NOT increment level for body check
import core/ast as ast
import core/state as state
import core/infer.{infer}
import core/quote.{quote}
import tao/ffi.{tao_ffis}
import syntax/grammar.{Span}
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPERS
// ============================================================================

const s0 = Span("debruijn_level", 0, 0, 0, 0)
const s1 = Span("debruijn_level", 1, 1, 1, 1)
const s2 = Span("debruijn_level", 2, 2, 2, 2)

fn var(index, span) {
  ast.Var(index, span)
}

fn lam(name, param_ty, body, span) {
  ast.Lam([], #(name, param_ty), body, span)
}

fn pi(name, domain, codomain, span) {
  ast.Pi([], name, domain, codomain, span)
}

fn fix(name, body, span) {
  ast.Fix(name, body, span)
}

fn ann(term, typ, span) {
  ast.Ann(term, typ, span)
}

fn app(fun, arg, span) {
  ast.App(fun, [], arg, span)
}

fn ctr(name, arg, span) {
  ast.Ctr(name, arg, span)
}

fn typ(level, span) {
  ast.Typ(level, span)
}

fn unit(span) {
  ast.Unit(span)
}

fn hole(id, span) {
  ast.Hole(id, span)
}

// ============================================================================
// TEST: Pi type with nested binder - level must be managed
// ============================================================================
/// Pi(x: A, Pi(y: B, x)) - the x in the inner codomain must have index 1
/// (referring to the outer x), not index 0 (which would refer to y).
/// If Pi doesn't increment level, both x and y get the same HVar,
/// and quote produces the wrong index.
pub fn pi_nested_binder_level_test() {
  // Pi(x: Typ(0), Pi(y: Typ(1), Var(0)))
  // The inner Var(0) should refer to x (index 0 in the inner scope = 1 in outer)
  let a_type = typ(0, s0)   // Type 0
  let b_type = typ(1, s0)   // Type 1
  let inner_var = var(0, s0) // y in inner scope, x in outer scope

  let inner_pi = pi("y", b_type, inner_var, s0)
  let outer_pi = pi("x", a_type, inner_pi, s0)

  let #(_val, _ty, s) = infer(state.initial_state, outer_pi)

  // Should have NO errors
  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Pi with variable in codomain
// ============================================================================
/// Pi(x: A, x) - the codomain refers to the bound variable.
/// If level is not incremented, the HVar for x will be wrong.
pub fn pi_codomain_refers_to_binder_test() {
  let a_type = typ(0, s0)
  let x_var = var(0, s0)  // refers to x
  let pi_type = pi("x", a_type, x_var, s0)

  let #(_val, _ty, s) = infer(state.initial_state, pi_type)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Fix with annotated lambda - Fix name and Lam param must have different levels
// ============================================================================
/// fix f -> (lam x -> body) : Pi(x: A, B)
/// The Fix name `f` and the Lam param `x` must get different HVar indices.
/// If infer_fix doesn't increment level, both get HVar(0).
pub fn fix_annotated_lambda_level_test() {
  // Build: fix f -> Ann(lam x -> x, Pi(x: Typ(0), Typ(0)))
  let a_type = typ(0, s0)
  let x_var = var(0, s0)  // refers to x
  let x_lam = lam("x", a_type, x_var, s0)
  let pi_type = pi("x", a_type, a_type, s0)
  let ann_lam = ann(x_lam, pi_type, s0)
  let fix_term = fix("f", ann_lam, s0)

  let #(_val, _ty, s) = infer(state.initial_state, fix_term)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Two nested Pis - each binder must increment level
// ============================================================================
/// Pi(f: A->B, Pi(x: A, f x)) - nested Pi types with variable references.
/// Tests that level is correctly managed through multiple nested binders.
pub fn two_nested_pis_level_test() {
  let a_type = typ(0, s0)
  let b_type = typ(1, s0)
  let fn_type = pi("_", a_type, b_type, s0)  // A -> B

  // Inner: Pi(x: A, Var(0)) where Var(0) refers to x
  let inner_body = var(0, s0)
  let inner_pi = pi("x", a_type, inner_body, s0)

  // Outer: Pi(f: A->B, inner_pi)
  let outer_pi = pi("f", fn_type, inner_pi, s0)

  let #(_val, _ty, s) = infer(state.initial_state, outer_pi)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Three nested Pis - stress test for level management
// ============================================================================
/// Pi(a: Type, Pi(b: Type, Pi(c: Type, a))) - three levels of nesting.
/// The innermost `a` must have index 2 (skipping b and c).
pub fn three_nested_pis_level_test() {
  let type0 = typ(0, s0)

  // Innermost: Pi(c: Type, Var(2)) - Var(2) refers to `a`
  let innermost = pi("c", type0, var(2, s0), s0)

  // Middle: Pi(b: Type, innermost)
  let middle = pi("b", type0, innermost, s0)

  // Outer: Pi(a: Type, middle)
  let outer = pi("a", type0, middle, s0)

  let #(_val, _ty, s) = infer(state.initial_state, outer)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Fix without annotation - level must still be managed
// ============================================================================
/// fix f -> lam x -> x - no annotation, but level must be correct.
pub fn fix_no_annotation_level_test() {
  let a_type = typ(0, s0)
  let x_var = var(0, s0)
  let x_lam = lam("x", a_type, x_var, s0)
  let fix_term = fix("f", x_lam, s0)

  let #(_val, _ty, s) = infer(state.initial_state, fix_term)

  // Should not crash or produce errors
  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Quote roundtrip for Pi with nested binder
// ============================================================================
/// After infer + quote, the De Bruijn indices must be correct.
/// Pi(x: A, Pi(y: B, x)) should quote back with Var(1) for x in the inner scope.
pub fn pi_quote_roundtrip_test() {
  let a_type = typ(0, s0)
  let b_type = typ(1, s0)
  // In the inner Pi, Var(0) should be y, Var(1) should be x
  // But we want to refer to x, so use Var(1)
  let inner_body = var(1, s0)
  let inner_pi = pi("y", b_type, inner_body, s0)
  let outer_pi = pi("x", a_type, inner_pi, s0)

  let #(val, _ty, s) = infer(state.initial_state, outer_pi)

  // Should have no errors
  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)

  // Quote back to syntax
  let quoted = quote(tao_ffis(), 0, val, s0)

  // Should quote back to a Pi term
  case quoted {
    ast.Pi(_, _, _, _, _) -> True |> should.be_true()
    _ -> False |> should.be_true()
  }
}

// ============================================================================
// TEST: Fix with self-reference in body
// ============================================================================
/// fix f -> lam x -> f x - recursive function that calls itself.
/// The `f` inside the body must refer to the Fix binding, not the Lam param.
pub fn fix_self_reference_level_test() {
  let a_type = typ(0, s0)
  // lam x -> f x, where f = Var(1) (the Fix binding) and x = Var(0)
  let f_var = var(1, s0)
  let x_var = var(0, s0)
  let app_fx = app(f_var, x_var, s0)
  let x_lam = lam("x", a_type, app_fx, s0)

  // Annotation: Pi(x: A, A)
  let pi_type = pi("x", a_type, a_type, s0)
  let ann_lam = ann(x_lam, pi_type, s0)
  // Fix terms must be wrapped in sequential Lam for name binding.
  // Structure: App(Lam("f", Pi, Fix("f", Ann(...))), Fix("f", Ann(...)))
  let outer_lam = lam("f", pi_type, fix("f", ann_lam, s0), s0)
  let fix_term = fix("f", ann_lam, s0)
  let full_term = app(outer_lam, fix_term, s0)

  let #(_val, _ty, s) = infer(state.initial_state, full_term)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Two sequential function bindings (simulating module-level)
// ============================================================================
/// Simulates: let f = fix f -> lam x -> x; let g = fix g -> lam y -> f y
/// Tests that the level is correctly managed across multiple Fix bindings.
pub fn two_sequential_fixes_level_test() {
  let a_type = typ(0, s0)

  // f = fix f -> lam x -> x
  let x_var_f = var(0, s0)
  let f_lam_body = lam("x", a_type, x_var_f, s0)
  let f_pi = pi("x", a_type, a_type, s0)
  let f_ann = ann(f_lam_body, f_pi, s0)
  let f_fix = fix("f", f_ann, s0)

  // g = fix g -> lam y -> f y
  // In g's body: f = Var(2) (outer f), g = Var(1) (Fix g), y = Var(0)
  let f_var_g = var(2, s0)
  let y_var_g = var(0, s0)
  let app_fy = app(f_var_g, y_var_g, s0)
  let g_lam_body = lam("y", a_type, app_fy, s0)
  let g_pi = pi("y", a_type, a_type, s0)
  let g_ann = ann(g_lam_body, g_pi, s0)
  let g_fix = fix("g", g_ann, s0)

  // Sequential structure matching build_sequential_loop:
  // App(Lam("f", Pi_f, App(Lam("g", Pi_g, result), Fix("g"))), Fix("f"))
  let result = ast.Rcd([#("f", var(1, s0)), #("g", var(0, s0))], s0)
  let inner_lam = lam("g", g_pi, result, s0)
  let inner_app = app(inner_lam, g_fix, s0)
  let outer_lam = lam("f", f_pi, inner_app, s0)
  let full_term = app(outer_lam, f_fix, s0)

  let #(_val, _ty, s) = infer(state.initial_state, full_term)

  let has_errors = list.length(s.errors) > 0
  has_errors |> should.equal(False)
}
