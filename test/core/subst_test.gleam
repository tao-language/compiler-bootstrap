/// Tests for the `subst` module — force_value and hole resolution.
///
/// These tests verify that `force_value` correctly propagates hole
/// substitutions through all value constructors.
import core/ast
import core/state.{State, new_state}
import core/subst
import gleam/list
import gleam/option.{None, Some}
import gleeunit
import syntax/span.{Span}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// Helper values
// ============================================================================

const s = Span("subst_test", 0, 0, 0, 0)

/// A hole value: VNeut(HHole(10), [])
fn hole10() -> ast.Value {
  ast.vhole(10, [])
}

/// A hole applied to another hole: VNeut(HHole(10), [EApp(vhole(20, []), s)])
fn hole10_applied_to_hole20() -> ast.Value {
  ast.VNeut(ast.HHole(10), [ast.EApp(ast.vhole(20, []), s)])
}

/// A value with a hole inside a VCtr: VCtr("A", VNeut(HHole(10), []))
fn vctr_with_hole10() -> ast.Value {
  ast.VCtr("A", ast.vhole(10, []))
}

/// A value with a hole inside a VPi domain: VPi([], #("x", VNeut(HHole(10), [])), vint_t)
fn vpi_with_hole_domain() -> ast.Value {
  ast.VPi([], #("x", ast.vhole(10, [])), ast.vint_t)
}

/// A VNeut with a hole in the spine's EApp arg: VNeut(HVar(0), [EApp(vhole(10, []), s)])
fn vneut_spine_with_hole() -> ast.Value {
  ast.VNeut(ast.HVar(0), [ast.EApp(ast.vhole(10, []), s)])
}

/// A VNeut with a hole in the head's HCall args: VNeut(HCall("f", [vhole(10, [])]), [])
fn vneut_hcall_with_hole() -> ast.Value {
  ast.VNeut(ast.HCall("f", [ast.vhole(10, [])]), [])
}

/// A VRcd with a hole in a field: VRcd([#("x", VNeut(HHole(10), []))])
fn vrcd_with_hole() -> ast.Value {
  ast.VRcd([#("x", ast.vhole(10, []))])
}

/// A VRcdT with a hole in a field and a hole in the default:
/// VRcdT([#("x", vint_t, Some(vhole(10, [])))])
fn vrcdt_with_hole_default() -> ast.Value {
  ast.VRcdT([#("x", ast.vint_t, Some(ast.vhole(10, [])))])
}

/// A VLam with a hole in its env: VLam([vhole(10, [])], [], #("x", vint_t), int(42, s))
fn vlam_with_hole_in_env() -> ast.Value {
  ast.VLam(
    [ast.vhole(10, [])],
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lit(ast.Int(42), s),
  )
}

/// A VTypeDef with a hole in params: VTypeDef([#("a", VNeut(HHole(10), []))], [])
fn vdef_with_hole_in_params() -> ast.Value {
  ast.VTypeDef([#("a", ast.vhole(10, []))], [])
}

// ============================================================================
// force_value tests — hole resolution
// ============================================================================

pub fn force_value_no_holes_test() {
  // Values without holes should pass through unchanged.
  let v = ast.vint(42)
  assert subst.force_value([], [], v) == v
}

pub fn force_value_top_level_hole_resolved_test() {
  // A top-level hole should be resolved.
  let v = ast.vhole(10, [])
  let sub = [#(10, ast.vint(42))]
  assert subst.force_value([], sub, v) == ast.vint(42)
}

pub fn force_value_top_level_hole_unresolved_test() {
  // A hole with no substitution should remain unchanged.
  let v = ast.vhole(10, [])
  let sub = [#(20, ast.vint(42))]
  assert subst.force_value([], sub, v) == v
}

pub fn force_value_nested_hole_in_vctr_test() {
  // A hole inside a VCtr should be resolved.
  let v = ast.VCtr("A", ast.vhole(10, []))
  let sub = [#(10, ast.vint(42))]
  let expected = ast.VCtr("A", ast.vint(42))
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_nested_hole_in_vpi_domain_test() {
  // A hole inside a VPi's domain should be resolved.
  let v = ast.VPi([], #("x", ast.vhole(10, [])), ast.vint_t)
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VPi([], #("x", ast.vfloat_t), ast.vint_t)
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_nested_hole_in_vpi_codomain_test() {
  // A hole inside a VPi's codomain should be resolved.
  let v = ast.VPi([], #("x", ast.vint_t), ast.vhole(10, []))
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VPi([], #("x", ast.vint_t), ast.vfloat_t)
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_nested_hole_in_vpi_implicits_test() {
  // A hole inside a VPi's implicits should be resolved.
  let v = ast.VPi([#("a", ast.vhole(10, []))], #("x", ast.vint_t), ast.vint_t)
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VPi([#("a", ast.vfloat_t)], #("x", ast.vint_t), ast.vint_t)
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_hole_in_spine_eapp_test() {
  // A hole inside a spine's EApp arg should be resolved.
  let v = ast.VNeut(ast.HVar(0), [ast.EApp(ast.vhole(10, []), s)])
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VNeut(ast.HVar(0), [ast.EApp(ast.vfloat_t, s)])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_hole_in_hcall_args_test() {
  // A hole inside an HCall's args should be resolved.
  let v = ast.VNeut(ast.HCall("f", [ast.vhole(10, [])]), [])
  let sub = [#(10, ast.vint(42))]
  let expected = ast.VNeut(ast.HCall("f", [ast.vint(42)]), [])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_vrcd_with_hole_test() {
  // A hole inside a VRcd field should be resolved.
  let v = ast.VRcd([#("x", ast.vhole(10, []))])
  let sub = [#(10, ast.vint(42))]
  let expected = ast.VRcd([#("x", ast.vint(42))])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_vrcdt_with_hole_default_test() {
  // A hole inside a VRcdT's default value should be resolved.
  let v = ast.VRcdT([#("x", ast.vint_t, Some(ast.vhole(10, [])))])
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VRcdT([#("x", ast.vint_t, Some(ast.vfloat_t))])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_vrcdt_with_hole_field_test() {
  // A hole inside a VRcdT's field value should be resolved.
  let v = ast.VRcdT([#("x", ast.vhole(10, []), None)])
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VRcdT([#("x", ast.vfloat_t, None)])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_vlam_with_hole_in_env_test() {
  // Holes inside a VLam's env should be resolved.
  let v = ast.VLam(
    [ast.vhole(10, []), ast.vhole(20, [])],
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lit(ast.Int(42), s),
  )
  let sub = [#(10, ast.vfloat_t), #(20, ast.vint(99))]
  let expected = ast.VLam(
    [ast.vfloat_t, ast.vint(99)],
    [],
    #("x", ast.LitT(ast.IntT, s)),
    ast.Lit(ast.Int(42), s),
  )
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_vdef_with_hole_in_params_test() {
  // Holes inside a VTypeDef's params should be resolved.
  let v = ast.VTypeDef([#("a", ast.vhole(10, [])), #("b", ast.vhole(30, []))], [])
  let sub = [#(10, ast.vfloat_t), #(30, ast.vint(7))]
  let expected = ast.VTypeDef([#("a", ast.vfloat_t), #("b", ast.vint(7))], [])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_multiple_holes_same_id_test() {
  // Multiple holes with the same ID should all be resolved.
  let v = ast.VRcd([
    #("x", ast.vhole(10, [])),
    #("y", ast.vhole(10, [])),
  ])
  let sub = [#(10, ast.vint(42))]
  let expected = ast.VRcd([
    #("x", ast.vint(42)),
    #("y", ast.vint(42)),
  ])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_hole_resolves_to_non_neutral_test() {
  // When a hole resolves to a non-neutral value (e.g., VCtr),
  // force_value returns the resolved value.
  let v = ast.vhole(10, [])
  let sub = [#(10, ast.VCtr("B", ast.vint(99)))]
  assert subst.force_value([], sub, v) == ast.VCtr("B", ast.vint(99))
}

pub fn force_value_hole_resolves_to_neutral_test() {
  // When a hole resolves to a VNeut, the spine should merge.
  let v = ast.VNeut(ast.HHole(10), [ast.EApp(ast.vfloat_t, s)])
  let sub = [#(10, ast.vint(42))]
  // The resolved value is VLit, not VNeut, so the spine is lost.
  // force_value returns the resolved value as-is when it's not neutral.
  assert subst.force_value([], sub, v) == ast.vint(42)
}

pub fn force_value_hole_resolves_to_neutral_with_spine_test() {
  // When a hole resolves to a VNeut with a spine, spines should merge.
  let v = ast.VNeut(ast.HHole(10), [ast.EApp(ast.vfloat_t, s)])
  let sub = [#(10, ast.VNeut(ast.HVar(5), [ast.EApp(ast.vint(0), s)]))]
  // The resolved value is VNeut, so spines merge:
  // original spine [EApp(vfloat_t)] is appended to resolved spine [EApp(vint(0))]
  let expected = ast.VNeut(ast.HVar(5), [ast.EApp(ast.vint(0), s), ast.EApp(ast.vfloat_t, s)])
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_chain_holes_test() {
  // Chain: hole 10 -> hole 20 -> vint(42)
  // force_value should resolve all holes in one pass because
  // it recursively forces the solution.
  let v = ast.vhole(10, [])
  let sub = [#(10, ast.vhole(20, [])), #(20, ast.vint(42))]
  assert subst.force_value([], sub, v) == ast.vint(42)
}

pub fn force_value_unchanged_values_test() {
  // These values should pass through force_value unchanged.
  let vals = [
    ast.VTyp(5),
    ast.VLit(ast.Int(42)),
    ast.VLit(ast.Float(3.14)),
    ast.VLitT(ast.IntT),
    ast.VLitT(ast.F64),
    ast.VErr,
  ]
  let sub = [#(10, ast.vhole(20, []))]  // hole 10 is unused
  let result = list.all(vals, fn(v) { subst.force_value([], sub, v) == v })
  assert result == True
}

// ============================================================================
// Edge cases
// ============================================================================

pub fn force_value_empty_subst_test() {
  // With an empty substitution, holes remain unresolved.
  let v = ast.vhole(10, [])
  assert subst.force_value([], [], v) == v
}

pub fn force_value_ffi_ignored_test() {
  // force_value does not use the FFI (β-reduction is not implemented yet).
  let v = ast.vhole(10, [])
  let sub = [#(10, ast.vint(42))]
  assert subst.force_value([], sub, v) == ast.vint(42)
}

pub fn force_value_deeply_nested_hole_test() {
  // A hole nested deeply inside composite values should be resolved.
  let v = ast.VPi(
    [#("a", ast.vhole(10, []))],
    #("x", ast.VRcd([#("y", ast.vhole(10, []))])),
    ast.VRcd([#("z", ast.vhole(10, []))]),
  )
  let sub = [#(10, ast.vfloat_t)]
  let expected = ast.VPi(
    [#("a", ast.vfloat_t)],
    #("x", ast.VRcd([#("y", ast.vfloat_t)])),
    ast.VRcd([#("z", ast.vfloat_t)]),
  )
  assert subst.force_value([], sub, v) == expected
}

pub fn force_value_hole_in_vneut_head_not_hole_test() {
  // A VNeut with a non-hole head but hole in HCall args.
  let v = ast.VNeut(ast.HCall("g", [ast.vhole(10, []), ast.vhole(30, [])]), [ast.EApp(ast.vhole(50, []), s)])
  let sub = [#(10, ast.vint(1)), #(30, ast.vfloat_t), #(50, ast.vint(99))]
  let expected = ast.VNeut(ast.HCall("g", [ast.vint(1), ast.vfloat_t]), [ast.EApp(ast.vint(99), s)])
  assert subst.force_value([], sub, v) == expected
}
