/// Regression tests for the deferred-constraint machinery (finding B).
///
/// A function body desugars to a match on the neutral `__args` record,
/// whose inferred type is an `NMatch`. Checking the declared return
/// annotation against it used to hit the unifier's neutral catch-all and
/// be silently discarded, so *ill-typed* annotated bodies passed. The
/// constraint is now recorded in the context's deferred queue and
/// discharged at resolve time: an `NMatch` is checked against *some* case
/// body (exists semantics), which is where the conflicting variant
/// return type (`Expr(Bool) ≠ Expr(Int)`) surfaces as an error.
///
/// These tests pin the soundness of that discharge. The matching
/// well-typed cases (ADTs, GADT evaluators, sibling parameters) live in
/// `adt_test.gleam` and must keep passing.
import core/context.{Context, new_ctx}
import core/error.{display, display_syntax}
import core/ffi
import gleam/list
import gleam/option.{None}
import gleam/string
import tao/ast.{type Module}
import tao/compile
import tao/load
import tao/parse as p

const nl = "\n"

const expr_type =
  "type Expr(a) { | LitInt(Int) -> Expr(Int) | LitBool(Bool) -> Expr(Bool) | IsZero(Expr(Int)) -> Expr(Bool) }"

// ============================================================================
// Ill-typed: the annotation must be checked against the case bodies
// ============================================================================

/// B1: `LitBool(True) : Expr(Bool)`, not `Expr(Int)`. The return
/// annotation is a neutral match vs `Expr(Int)`, so the conflict only
/// surfaces when the constraint is discharged against the case body.
pub fn b1_fn_return_annot_litbool_test() {
  let src = expr_type
    <> nl
    <> "fn f() -> Expr(Int) ="
    <> nl
    <> "LitBool(True)"
  assert check(src) != []
}

/// B1 + constructor signature: `IsZero(LitBool(True))` cannot be
/// `Expr(Int)` — the `IsZero` variant returns `Expr(Bool)`, and its
/// argument must be `Expr(Int)`.
pub fn b1_fn_return_annot_iszero_litbool_test() {
  let src = expr_type
    <> nl
    <> "fn f() -> Expr(Int) ="
    <> nl
    <> "IsZero(LitBool(True))"
  assert check(src) != []
}

// ============================================================================
// Ill-typed: constructor signatures at the dependent use
// ============================================================================

/// C: the constructor signature is enforced where the value is used in a
/// typed context: `f() : Ctr("IsZero", ...)`, checked against `Expr(Bool)`
/// through the `IsZero` variant (arg must be `Expr(Int)`, return is
/// `Expr(Bool)`).
pub fn c_ctor_signature_at_dependent_use_test() {
  let src =
    expr_type
    <> nl
    <> "fn f() ="
    <> nl
    <> "IsZero(LitBool(True))"
    <> nl
    <> "let g: Expr(Bool) = f()"
  assert check(src) != []
}

// ============================================================================
// Ill-typed: impossible GADT cases (already caught at pattern check; kept
// as regression coverage next to the B tests).
// ============================================================================

/// A `LitInt` case against `Expr(Bool)` is impossible — the variant's
/// return type `Expr(Int)` conflicts with the scrutinee type `Expr(Bool)`.
pub fn impossible_litint_case_test() {
  let src = expr_type
    <> nl
    <> "fn f(e: Expr(Bool)) -> Int ="
    <> nl
    <> "match e {"
    <> nl
    <> "| LitInt(n) => n"
    <> nl
    <> "| _ => 0"
    <> nl
    <> "}"
  assert check(src) != []
}

// ============================================================================
// Well-typed: the discharge must not create false positives
// ============================================================================

/// A well-typed evaluator over the GADT: the annotation `Int` vs the
/// neutral body match discharges cleanly (a case body whose type is itself
/// a neutral match simply re-defers, it does not error).
pub fn well_typed_gadt_evaluator_test() {
  let src = expr_type
    <> nl
    <> "fn f(e: Expr(Int)) -> Int ="
    <> nl
    <> "match e {"
    <> nl
    <> "| LitInt(n) => n"
    <> nl
    <> "| _ => 0"
    <> nl
    <> "}"
  assert check(src) == []
}

/// An overloaded-operator dependent dispatch (an `NMatch` whose cases
/// intentionally have *different* types) must not be reported: checking it
/// against its result type uses exists semantics.
pub fn well_typed_overload_dispatch_test() {
  let src =
    "extern int_add(Int, Int) -> Int"
    <> nl
    <> "extern float_add(Float, Float) -> Float"
    <> nl
    <> "fn (+) {"
    <> nl
    <> "| int_add(Int, Int)"
    <> nl
    <> "| float_add(Float, Float)"
    <> nl
    <> "}"
    <> nl
    <> "fn f(x: Int) -> Int = x + 1"
    <> nl
    <> "fn g(x: Float) -> Float = x + 1.0"
  assert check(src) == []
}

/// A neutral match annotated with the prelude's `Bool`: the case bodies
/// `True`/`False` are bare constructor tags that only unify with the
/// expected `Bool` through the prelude's `Bool` type definition
/// (`lib/prelude/v0.0.1/bool.tao`).
pub fn well_typed_bool_annotated_match_test() {
  // A concrete scrutinee: the match reduces to the bare `True` tag, which
  // only unifies with the expected `Bool` through the prelude's `Bool`
  // type definition.
  let src =
    "let b: Bool ="
    <> nl
    <> "match 5 {"
    <> nl
    <> "| 5 => True"
    <> nl
    <> "| _ => False"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A function whose body is a neutral match annotated with the
/// prelude's `Bool`: the annotation discharges against the (neutral)
/// case bodies without a false positive.
pub fn well_typed_bool_annotated_fn_match_test() {
  let src =
    "fn is_empty(l) -> Bool ="
    <> nl
    <> "match l {"
    <> nl
    <> "| Nil => True"
    <> nl
    <> "| _ => False"
    <> nl
    <> "}"
  assert check(src) == []
}

/// A well-typed function whose result is a neutral match annotated with
/// `Int`: the annotation is discharged against the (neutral) case bodies
/// without error.
pub fn well_typed_annotated_match_test() {
  let src =
    "fn f(x) -> Int ="
    <> nl
    <> "match x {"
    <> nl
    <> "| 0 => 1"
    <> nl
    <> "| _ => 2"
    <> nl
    <> "}"
  assert check(src) == []
}

// ============================================================================
// CLI hardening
// ============================================================================

/// An undefined variable is reported as an error, not a panic: the name
/// is not a definition of the module, so the definition phase must
/// degrade gracefully instead of crashing the host.
pub fn undefined_variable_reported_test() {
  let src = "fn f() -> Int =" <> nl <> "nope + 1"
  assert check(src) != []
}

// ============================================================================
// Harness
// ============================================================================

/// Compile an in-memory module against the prelude (as the `debug-file`
/// CLI does: the prelude modules are compiled together with the module
/// and implicitly imported into it) and return the reported errors (or a
/// parse error message).
fn check(source: String) -> List(String) {
  case p.statements("scratch", source) {
    Ok(stmts) -> {
      let #(prelude, _load_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      let mods: List(Module) =
        list.append([#("scratch", stmts)], prelude)
        |> load.implicit_prelude_imports(_, prelude)
      let ctx =
        Context(..new_ctx, ffi: ffi.build)
        |> compile.modules(mods)
      list.map(ctx.errors, fn(err) { display(ffi.build, ctx.types, err) })
    }
    Error(err) -> ["PARSE: " <> display_syntax(err)]
  }
}
