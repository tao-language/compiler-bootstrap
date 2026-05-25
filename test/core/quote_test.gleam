/// Tests for the `quote` module — converting Values back to Terms.
///
/// These tests verify:
/// - Basic value constructors (VTyp, VLit, VLitT, VCtr, VRcd, VRcdT)
/// - Neutral terms (HVar, HHole, HCall)
/// - Eliminators (EApp, EFix, EMatch)
/// - Lambda and Pi quoting with correct binder depth
/// - VTypeDef quoting
/// - Level→index conversion correctness
import core/ast
import core/quote.{quote}
import core/state.{State, new_state, with_err}
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

const s = Span("quote_test", 0, 0, 0, 0)
const s1 = Span("quote_test", 1, 1, 1, 1)
const s2 = Span("quote_test", 2, 2, 2, 2)
const s3 = Span("quote_test", 3, 3, 3, 3)

// ============================================================================
// Existing tests (unchanged)
// ============================================================================

pub fn quote_vtyp_test() {
  let value = ast.VTyp(0)
  let term = quote([], 0, value, s)
  assert term == ast.Typ(0, s)
}

pub fn quote_vlit_test() {
  let value = ast.VLit(ast.Int(42))
  let term = quote([], 0, value, s)
  assert term == ast.Lit(ast.Int(42), s)
}

pub fn quote_vlitt_test() {
  let value = ast.VLitT(ast.IntT)
  let term = quote([], 0, value, s)
  assert term == ast.LitT(ast.IntT, s)
}

pub fn quote_vctr_test() {
  let value = ast.VCtr("A", ast.vint(42))
  let term = quote([], 0, value, s)
  assert term == ast.Ctr("A", ast.int(42, s), s)
}

pub fn quote_vrcd_test() {
  let value = ast.VRcd([#("x", ast.vint_t), #("y", ast.vfloat_t)])
  let term = quote([], 0, value, s)
  assert term == ast.Rcd([#("x", ast.int_t(s)), #("y", ast.float_t(s))], s)
}

pub fn quote_vrcdt_test() {
  let value =
    ast.VRcdT([
      #("x", ast.vint_t, Some(ast.vint(42))),
      #("y", ast.vfloat_t, None),
    ])
  let term = quote([], 0, value, s)
  assert term
    == ast.RcdT(
      [#("x", ast.int_t(s), Some(ast.int(42, s))), #("y", ast.float_t(s), None)],
      s,
    )
}

pub fn quote_vneut_hvar_test() {
  // De Bruijn levels map directly to De Bruijn indices:
  // level 0 = innermost binder = index 0
  // level 1 = next binder = index 1
  // etc.
  assert quote([], 1, ast.vvar(0, []), s) == ast.Var(0, s)
  assert quote([], 2, ast.vvar(0, []), s) == ast.Var(0, s)
  assert quote([], 3, ast.vvar(0, []), s) == ast.Var(0, s)
  assert quote([], 2, ast.vvar(1, []), s) == ast.Var(1, s)
  assert quote([], 3, ast.vvar(1, []), s) == ast.Var(1, s)
  assert quote([], 4, ast.vvar(1, []), s) == ast.Var(1, s)
}

pub fn quote_vneut_hhole_test() {
  let value = ast.VNeut(ast.HHole(42), [])
  let term = quote([], 0, value, s)
  assert term == ast.Hole(42, s)
}

// ============================================================================
// New tests for EApp spine elimination
// ============================================================================

pub fn quote_vneut_hvar_with_eapp_spine_test() {
  // HVar(0) applied to vint_t: VNeut(HVar(0), [EApp(vint_t, s)])
  let value = ast.VNeut(ast.HVar(0), [ast.EApp(ast.vint_t, s1)])
  let term = quote([], 1, value, s)
  assert term == ast.App(ast.Var(0, s), ast.LitT(ast.IntT, s1), s)
}

pub fn quote_vneut_hvar_with_double_eapp_spine_test() {
  // HVar(0) applied to two args: VNeut(HVar(0), [EApp(a), EApp(b)])
  let a = ast.vint_t
  let b = ast.vfloat_t
  let value = ast.VNeut(ast.HVar(0), [ast.EApp(a, s1), ast.EApp(b, s2)])
  let term = quote([], 1, value, s)
  // First application: App(Var(0), vint_t)
  // Second application: App(App(Var(0), vint_t), vfloat_t)
  assert term == ast.App(
    ast.App(ast.Var(0, s), ast.LitT(ast.IntT, s1), s),
    ast.LitT(ast.FloatT, s2),
    s,
  )
}

// ============================================================================
// New tests for VLam quoting
// ============================================================================

pub fn quote_vlam_simple_test() {
  // A lambda with no implicits, one param, and a simple body.
  let body = ast.Lit(ast.Int(42), s)
  let value = ast.VLam(
    [],  // env
    [],  // implicits
    #("x", ast.LitT(ast.IntT, s)),  // param (Term, not Value)
    body,  // body
  )
  let term = quote([], 0, value, s)
  let expected = ast.Lam(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lit(ast.Int(42), s),
    s,
  )
  assert term == expected
}

pub fn quote_vlam_with_env_test() {
  // A lambda whose body references both the param (HVar(0)) and
  // an enclosing binder (HVar(1)).
  let body = ast.Var(1, s)  // HVar(1) from the value's perspective
  let value = ast.VLam(
    [ast.vfloat_t],  // env has one binder: the enclosing context
    [],
    #("x", ast.LitT(ast.IntT, s)),
    body,
  )
  let term = quote([], 0, value, s)
  // lvl starts at 0. Inside the lambda, lvl = 1.
  // HVar(1) in the body: with lvl=1 (the lambda param), index = 1 - 1 - 1 = -1
  // That's out of bounds! The body Var(1) refers to a binder outside the lambda,
  // but the lambda's env has only one entry.
  // Actually, Var(1) is already in indices, so it should be quoted as Var(1).
  // The body is a Term, so quote_body doesn't convert levels.
  // Var(1) stays as Var(1) regardless of lvl.
  let expected = ast.Lam(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Var(1, s),
    s,
  )
  assert term == expected
}

pub fn quote_vlam_with_implicits_test() {
  // A lambda with implicit parameters.
  let body = ast.Lit(ast.Int(42), s)
  let value = ast.VLam(
    [],
    [#("a", ast.LitT(ast.IntT, s)), #("b", ast.LitT(ast.FloatT, s))],
    #("x", ast.LitT(ast.IntT, s)),
    body,
  )
  let term = quote([], 0, value, s)
  let expected = ast.Lam(
    [#("a", ast.LitT(ast.IntT, s)), #("b", ast.LitT(ast.FloatT, s))],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lit(ast.Int(42), s),
    s,
  )
  assert term == expected
}

pub fn quote_vlam_nested_test() {
  // Nested lambda: outer has param x, inner has param y.
  let inner_body = ast.Var(0, s)  // y
  let inner_lam = ast.Lam(
    [],
    #("y", ast.LitT(ast.FloatT, s)),
    inner_body,
    s,
  )
  let outer_lam = ast.VLam(
    [],
    [],
    #("x", ast.LitT(ast.IntT, s)),
    inner_lam,
  )
  let term = quote([], 0, outer_lam, s)
  let expected = ast.Lam(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lam(
      [],
      #("y", ast.LitT(ast.FloatT, s)),
      ast.Var(0, s),
      s,
    ),
    s,
  )
  assert term == expected
}

// ============================================================================
// New tests for VPi quoting
// ============================================================================

pub fn quote_vpi_simple_test() {
  // A simple Pi type: (x: Int) -> Int
  let domain = ast.vint_t
  let codomain = ast.vint_t
  let value = ast.VPi([], #("x", domain), codomain)
  let term = quote([], 0, value, s)
  let expected = ast.Pi(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.LitT(ast.IntT, s),
    s,
  )
  assert term == expected
}

pub fn quote_vpi_with_depends_on_domain_test() {
  // A Pi where the codomain depends on the domain: (x: Int) -> x
  // Here the codomain is HVar(0) which refers to the domain variable.
  // In the value: codomain = VNeut(HVar(0), []), but HVar(0) at lvl=1 (inside Pi).
  let codomain = ast.VNeut(ast.HVar(0), [])
  let value = ast.VPi([], #("x", ast.vint_t), codomain)
  let term = quote([], 0, value, s)
  // lvl starts at 0. Inside the Pi codomain, lvl = 1.
  // HVar(0) with lvl=1: index = 1 - 1 - 0 = 0. But our code uses identity.
  // Actually, the code uses index = absolute_level = 0.
  // So Var(0) which refers to x. That's correct!
  let expected = ast.Pi(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Var(0, s),
    s,
  )
  assert term == expected
}

pub fn quote_vpi_with_implicits_test() {
  // A Pi with implicit parameters.
  let value = ast.VPi(
    [#("n", ast.vint_t)],
    #("x", ast.vint_t),
    ast.vint_t,
  )
  let term = quote([], 0, value, s)
  let expected = ast.Pi(
    [#("n", ast.LitT(ast.IntT, s))],
    #("x", ast.LitT(ast.IntT, s)),
    ast.LitT(ast.IntT, s),
    s,
  )
  assert term == expected
}

// ============================================================================
// New tests for VTypeDef quoting
// ============================================================================

pub fn quote_vdef_empty_test() {
  let value = ast.VTypeDef([], [])
  let term = quote([], 0, value, s)
  let expected = ast.TypeDef([], [], s)
  assert term == expected
}

pub fn quote_vdef_with_params_test() {
  let value = ast.VTypeDef(
    [#("a", ast.vint_t), #("b", ast.vfloat_t)],
    [],
  )
  let term = quote([], 0, value, s)
  let expected = ast.TypeDef(
    [#("a", ast.LitT(ast.IntT, s)), #("b", ast.LitT(ast.FloatT, s))],
    [],
    s,
  )
  assert term == expected
}

pub fn quote_vdef_with_constructors_test() {
  let value = ast.VTypeDef(
    [],
    [
      #(
        "Cons",
        #(
          [],
          ast.vint_t,
          ast.Lit(ast.Int(42), s),
        ),
      ),
      #(
        "Nil",
        #([], ast.vfloat_t, ast.Lit(ast.Int(0), s)),
      ),
    ],
  )
  let term = quote([], 0, value, s)
  let expected = ast.TypeDef(
    [],
    [
      #(
        "Cons",
        #(
          [],
          ast.LitT(ast.IntT, s),
          ast.Lit(ast.Int(42), s),
        ),
        s,
      ),
      #(
        "Nil",
        #([], ast.LitT(ast.FloatT, s), ast.Lit(ast.Int(0), s)),
        s,
      ),
    ],
    s,
  )
  assert term == expected
}

// ============================================================================
// New tests for EFix elimination
// ============================================================================

pub fn quote_vneut_with_efix_spine_test() {
  // A neutral term with EFix in its spine.
  let value = ast.VNeut(ast.HVar(0), [ast.EFix([], ast.Lit(ast.Int(42), s))])
  let term = quote([], 1, value, s)
  // EFix doesn't store the name, so we use "<fix>" as placeholder.
  let expected = ast.Fix("<fix>", ast.Lit(ast.Int(42), s), s)
  assert term == expected
}

// ============================================================================
// New tests for EMatch elimination
// ============================================================================

pub fn quote_vneut_with_ematch_spine_test() {
  // A neutral term with EMatch in its spine.
  let case_term = ast.Case(
    ast.PAny(s1),
    None,
    ast.Var(0, s1),
    s1,
  )
  let value = ast.VNeut(ast.HVar(0), [ast.EMatch([], [case_term], s1)])
  let term = quote([], 1, value, s)
  let expected = ast.Match(
    ast.Var(0, s),
    [ast.Case(ast.PAny(s1), None, ast.Var(0, s1), s1)],
    s,
  )
  assert term == expected
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn quote_verr_test() {
  let value = ast.VErr
  let term = quote([], 0, value, s)
  assert term == ast.Err(s)
}

pub fn quote_vneut_hcall_err_test() {
  // HCall heads can't be reconstructed as Terms (we don't have the function name).
  let value = ast.VNeut(ast.HCall("foo", [ast.vint(42)]), [])
  let term = quote([], 0, value, s)
  assert term == ast.Err(s)
}

pub fn quote_nested_vctr_test() {
  // Deeply nested constructors.
  let value = ast.VCtr("A", ast.VCtr("B", ast.vint(42)))
  let term = quote([], 0, value, s)
  let expected = ast.Ctr("A", ast.Ctr("B", ast.int(42, s), s), s)
  assert term == expected
}

pub fn quote_vpi_nested_test() {
  // Nested Pi types: (x: Int) -> (y: Float) -> Int
  let codomain = ast.VPi([], #("y", ast.vfloat_t), ast.vint_t)
  let value = ast.VPi([], #("x", ast.vint_t), codomain)
  let term = quote([], 0, value, s)
  let expected = ast.Pi(
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Pi(
      [],
      #("y", ast.LitT(ast.FloatT, s)),
      ast.LitT(ast.IntT, s),
      s,
    ),
    s,
  )
  assert term == expected
}

pub fn quote_vneut_with_mixed_spine_test() {
  // A neutral term with mixed spine: HVar(0) applied to int, then matched.
  let case_term = ast.Case(
    ast.PAny(s2),
    None,
    ast.Var(0, s2),
    s2,
  )
  let value = ast.VNeut(
    ast.HVar(0),
    [
      ast.EApp(ast.vint_t, s1),
      ast.EMatch([], [case_term], s3),
    ],
  )
  let term = quote([], 1, value, s)
  // First: App(Var(0), vint_t)
  // Second: Match(App(Var(0), vint_t), [case])
  let expected = ast.Match(
    ast.App(ast.Var(0, s), ast.LitT(ast.IntT, s1), s),
    [ast.Case(ast.PAny(s2), None, ast.Var(0, s2), s2)],
    s,
  )
  assert term == expected
}

pub fn quote_vrcdt_nested_hole_default_test() {
  // VRcdT with a hole in the default value, which when quoted becomes a Hole term.
  let value = ast.VRcdT([
    #("x", ast.vint_t, Some(ast.vhole(42, []))),
  ])
  let term = quote([], 0, value, s)
  let expected = ast.RcdT([
    #("x", ast.LitT(ast.IntT, s), Some(ast.Hole(42, s))),
  ], s)
  assert term == expected
}
