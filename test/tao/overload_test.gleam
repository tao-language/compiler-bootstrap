/// End-to-end tests for function overloads (dependent dispatch) with
/// type names in choice patterns, module-qualified choices
/// (`bool._and`), and operator-named definitions (an overload or a
/// `let (and) = ...`).
///
/// These cover the pipeline that used to break in
/// `lib/prelude/v0.0.1/operators/and.tao` (see docs/overloads.md):
///
/// * a choice pattern field like `Bool` is a `Ctr` value (`#Bool{}`)
///   checked against the dispatch scrutinee's type `%Type` — the
///   unifier accepts a constructor application as a type when the tag
///   names a type definition or a variant of one (`unify`'s
///   Ctr-vs-Typ rule);
/// * at compile time `define.expand_overload_choices` rewrites the type
///   names in the choices into concrete constructor patterns (`Bool` →
///   `Bool`/`True`/`False`), so the *blind* runtime dispatch match (the
///   evaluator does no type lookups) selects the choice whose patterns
///   name the arguments' constructor types (`#True{}`/`#False{}` for
///   Bool arguments);
/// * a module that defines `and` locally while the prelude also exports
///   `and` (the `debug-file` flow loads the file both standalone and as
///   a prelude module) — the local definition must shadow the import
///   instead of sharing its module-record entry.
import core/context.{type Context, Context, new_ctx}
import core/error.{display, display_syntax}
import core/ffi
import core/format.{value as fmt_value}
import core/value.{type Value}
import gleam/list
import gleam/option.{None}
import gleam/string
import tao/ast.{type Module}
import tao/compile
import tao/load
import tao/parse as p
import tao/tests.{TestFail, TestNeutral, run_all}

const nl = "\n"

// ============================================================================
// Type-checking
// ============================================================================

/// The prelude's `and` definition: a module-qualified choice over the
/// `Bool` type.
pub fn and_overload_compiles_test() {
  let src =
    "import prelude/bool {Bool}"
    <> nl
    <> "fn (and) {"
    <> nl
    <> "| bool._and(Bool, Bool)"
    <> nl
    <> "}"
  assert check(src) == []
}

/// The `let` form: an operator name bound to a module-qualified
/// definition.
pub fn and_let_form_compiles_test() {
  let src = "import prelude/bool {Bool}" <> nl <> "let (and) = bool._and"
  assert check(src) == []
}

/// A choice pattern that names a name which is not a type definition is
/// a type error: the Ctr-as-Type rule is gated on a type definition, so
/// typos in choice types are reported instead of silently accepted.
pub fn overload_choice_unknown_type_test() {
  let src =
    "import prelude/bool {Bool}"
    <> nl
    <> "fn (and) {"
    <> nl
    <> "| bool._and(Nope, Nope)"
    <> nl
    <> "}"
  let errors = check(src)
  assert list.any(errors, fn(err) { string.contains(err, "type mismatch") })
}

// ============================================================================
// Evaluation (both forms dispatch on Bool and compute correctly)
// ============================================================================

pub fn and_overload_evaluates_test() {
  let src =
    "import prelude/bool {Bool}"
    <> nl
    <> "fn (and) {"
    <> nl
    <> "| bool._and(Bool, Bool)"
    <> nl
    <> "}"
    <> nl
    <> ">>> True and True    True"
    <> nl
    <> ">>> True and False   False"
    <> nl
    <> ">>> False and True   False"
    <> nl
    <> ">>> False and False  False"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

pub fn and_let_form_evaluates_test() {
  let src =
    "import prelude/bool {Bool}"
    <> nl
    <> "let (and) = bool._and"
    <> nl
    <> ">>> True and True    True"
    <> nl
    <> ">>> True and False   False"
    <> nl
    <> ">>> False and True   False"
    <> nl
    <> ">>> False and False  False"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

/// The local definition shadows the prelude's `and` (the prelude is
/// imported implicitly and also defines `and` in
/// `/prelude/operators/and`): the module's own definition is used, and
/// the import must not share the module record's entry for the name.
pub fn local_and_shadows_prelude_test() {
  let src =
    "import prelude/bool {Bool}"
    <> nl
    <> "fn (and) {"
    <> nl
    <> "| bool._and(Bool, Bool)"
    <> nl
    <> "}"
    <> nl
    <> ">>> True and False  False"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

// ============================================================================
// Harness
// ============================================================================

/// Type-check an in-memory module against the prelude (as the
/// `debug-file` CLI does: the prelude is compiled together with the
/// module and implicitly imported into it) and return the reported
/// errors.
fn check(source: String) -> List(String) {
  case p.statements("scratch", source) {
    Ok(stmts) -> {
      let #(prelude, _load_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      let mods: List(Module) =
        list.append([#("scratch", stmts)], prelude)
        |> load.implicit_prelude_imports(prelude)
      let ctx =
        Context(..new_ctx, ffi: ffi.build)
        |> compile.modules(mods)
      list.map(ctx.errors, fn(err) { display(ffi.build, ctx.types, err) })
    }
    Error(err) -> ["PARSE: " <> display_syntax(err)]
  }
}

/// Like `check`, but also runs the module's `>>> tests`, returning the
/// build errors and one line per failed or stuck test.
fn run(source: String) -> #(List(String), List(String)) {
  case p.statements("scratch", source) {
    Error(err) -> #(["PARSE: " <> display_syntax(err)], [])
    Ok(stmts) -> {
      let #(prelude, _load_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      let mods: List(Module) =
        list.append([#("scratch", stmts)], prelude)
        |> load.implicit_prelude_imports(prelude)
      let ctx =
        Context(..new_ctx, ffi: ffi.build)
        |> compile.modules(mods)
      let errors =
        list.map(ctx.errors, fn(err) { display(ffi.build, ctx.types, err) })
      let #(test_defs, ctx) = compile.tests(ctx, [#("scratch", stmts)])
      let summary = run_all(ctx, test_defs)
      let fails =
        list.flat_map(summary.results, fn(res) {
          case res {
            TestFail(name, got, _, _) -> [
              "  ✗ " <> name <> " got " <> display_value(ctx, got),
            ]
            TestNeutral(name, got, _, _) -> [
              "  ? " <> name <> " (stuck) got " <> display_value(ctx, got),
            ]
            _ -> []
          }
        })
      #(errors, fails)
    }
  }
}

fn display_value(ctx: Context, value: Value) -> String {
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  fmt_value(ffi.build, names, value, 80, 2)
}
