/// Tests for the `quote` module — converting Values back to Terms.
///
/// These tests verify:
/// - Basic value constructors (VTyp, VLit, VLitT, VCtr, VRcd, VRcdT)
/// - Neutral term (HVar) quoting with correct binder depth adjustment
/// - VTypeDef quoting
/// - Level→index conversion correctness
import core/literals as lit
import core/quote.{quote}
import core/term as tm
import core/value as v
import gleam/option.{None, Some}

// ============================================================================
// Basic value constructors
// ============================================================================

pub fn quote_vtyp_test() {
  let value = v.Typ(0)
  let term = quote([], [], value)
  assert term == tm.Typ(0)
}

pub fn quote_vlit_test() {
  let value = v.Lit(lit.Int(42))
  let term = quote([], [], value)
  assert term == tm.Lit(lit.Int(42))
}

pub fn quote_vlitt_test() {
  let value = v.LitT(lit.IntT)
  let term = quote([], [], value)
  assert term == tm.LitT(lit.IntT)
}

pub fn quote_vctr_test() {
  let value = v.Ctr("A", v.int(42))
  let term = quote([], [], value)
  assert term == tm.Ctr("A", tm.Lit(lit.Int(42)))
}

pub fn quote_vrcd_test() {
  let value = v.rcd_open([#("x", v.int_t), #("y", v.float_t)], None)
  let term = quote([], [], value)
  assert term
    == tm.rcd_open(
      [#("x", tm.LitT(lit.IntT)), #("y", tm.LitT(lit.FloatT))],
      None,
    )
}

// ============================================================================
// Neutral term quoting — tests DeBruijn index adjustment logic
// ============================================================================

pub fn quote_vneut_nvar_test() {
  // DeBruijn adjustment: index = len(env) - level - 1
  let q = fn(size, value) { quote([], v.env_push([], size), value) }
  assert q(1, v.var(0)) == tm.Var(0)
  assert q(2, v.var(0)) == tm.Var(1)
  assert q(3, v.var(0)) == tm.Var(2)
  assert q(2, v.var(1)) == tm.Var(0)
  assert q(3, v.var(1)) == tm.Var(1)
  assert q(4, v.var(1)) == tm.Var(2)
  assert q(3, v.var(2)) == tm.Var(0)
  assert q(4, v.var(2)) == tm.Var(1)
  assert q(5, v.var(2)) == tm.Var(2)
}

pub fn quote_vneut_nhole_test() {
  let value = v.hole_open([], Some(42))
  let term = quote([], [], value)
  assert term == tm.Hole(Some(42))
}

// ============================================================================
// Quantifier and neutral quoting
// ============================================================================

/// A `For` quotes to `For(param, body)` where the body is
/// *re-normalized* in the captured env plus one fresh parameter slot:
/// concrete captured values are inlined and captured neutrals re-quote
/// to the same index they had in the body frame.
pub fn quote_vfor_test() {
  let env = [v.int(5)]
  // Body frame is [param slot, int(5)]: Var(0) = the parameter,
  // Var(1) = the captured 5 (which evaluates to the literal).
  let for_ = v.For(env, #("a", v.Typ(0)), tm.App(tm.Var(0), tm.Var(1)))
  assert quote([], env, for_)
    == tm.For(#("a", tm.Typ(0)), tm.App(tm.Var(0), tm.int(5)))
}

/// A `Lam` quotes with the parameter type quoted in the captured env
/// and the body normalized in the parameter-extended frame.
pub fn quote_vlam_test() {
  let env = [v.int(5)]
  let lam = v.Lam(env, #("x", v.Typ(0)), tm.Var(0))
  assert quote([], env, lam) == tm.Lam(#("x", tm.Typ(0)), tm.Var(0))
}

/// `Pi`, like `Lam`, quotes to a Pi type arrow with the body normalized
/// in the parameter-extended captured frame.
pub fn quote_vpi_test() {
  let env = [v.int(5)]
  let pi = v.Pi(env, #("x", v.Typ(0)), tm.Var(0))
  assert quote([], env, pi) == tm.Pi(#("x", tm.Typ(0)), tm.Var(0))
}

/// `Fix` quotes to a fix term with the body normalized over the
/// fixpoint's own slot.
pub fn quote_vfix_test() {
  let env = [v.int(5)]
  let fix_ = v.Fix(env, "f", tm.Var(0))
  assert quote([], env, fix_) == tm.Fix("f", tm.Var(0))
}

/// A neutral application quotes to a plain `App` with the (neutral)
/// head and the (concrete) argument quoted in the same env.
pub fn quote_vneut_napp_test() {
  let env = v.env_push([], 1)
  let napp = v.Neut(v.NApp(v.NVar(0), v.int(5)))
  assert quote([], env, napp) == tm.App(tm.Var(0), tm.int(5))
}

/// A neutral match quotes to a plain `Match` term: the scrutinee and
/// the case bodies are quoted back to terms (the captured env is
/// re-used for the case bodies).
pub fn quote_vneut_nmatch_test() {
  let env = v.env_push([], 1)
  let cases = [tm.Case(tm.pint(1), None, tm.int(2))]
  let nmatch = v.match(env, v.Neut(v.NVar(0)), cases)
  assert quote([], env, nmatch)
    == tm.Match(tm.Var(0), [tm.Case(tm.pint(1), None, tm.int(2))])
}

/// A deferred call (an `extern` with no FFI entry) quotes back to a
/// `Call` term with the declared return type and the argument.
pub fn quote_vneut_ncall_test() {
  let ncall = v.call("ext", v.int_t, v.int(1))
  assert quote([], [], ncall) == tm.Call("ext", tm.int_t, tm.int(1))
}

/// A record value with a field default quotes to a record term carrying
/// the default.
pub fn quote_vrcd_default_test() {
  let field = #("a", #(v.int_t, Some(v.int(42))))
  assert quote([], [], v.Rcd([field], None))
    == tm.Rcd([#("a", #(tm.int_t, Some(tm.int(42))))], None)
}

/// A type definition quotes to a `TypeDef` term: parameter types and
/// variant types are quoted in the captured env, the variant argument
/// and return terms are kept as terms.
pub fn quote_vtypedef_test() {
  let param = #("a", v.Typ(0))
  let variant = #("C", v.Variant([], tm.Var(0), tm.ctr("T", [])))
  let td = v.TypeDef([], v.TypeDefinition(params: [param], arg: tm.Var(0), variants: [variant]))
  let expected_param = #("a", tm.Typ(0))
  let expected_variant = #("C", tm.Variant([], tm.Var(0), tm.ctr("T", [])))
  assert quote([], [], td)
    == tm.TypeDef(tm.TypeDefinition(params: [expected_param], arg: tm.Var(0), variants: [expected_variant]))
}
