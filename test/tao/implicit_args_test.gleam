/// Regression tests for implicit-argument (`fn f<a>(...)`) programs.
///
/// These pin the current behavior of the non-terminating-unification bug
/// (see docs/implicit-args.md) around the planned elaborate+infer
/// refactor:
///
/// * `*_passes_test` / `*_fails_test` — green today, must stay green
///   through the refactor;
/// * `two_*_terminate_test` / `multi_implicit_*_test` / the red
///   `*_passes_test` pairs — the acceptance gate: a hang hangs the whole
///   suite, so the hanging shapes are `todo` (failing, not hanging) with
///   the source commented in. When the fix lands, uncomment the body,
///   drop the `todo`, and the test goes green.
///
/// Harness: in-memory module compiled *together with the prelude* — the
/// exact trigger shape of the bug (any implicit-arg function + prelude).
import core/context.{type Context, Context, new_ctx}
import core/error.{display, display_syntax}
import core/ffi
import core/format.{value as fmt_value}
import core/value as v
import gleam/int
import gleam/list
import gleam/option.{None, Some, type Option}
import gleam/string
import tao/ast.{type Module}
import tao/compile
import tao/load
import tao/parse as p
import tao/tests.{TestFail, TestNeutral, run_all}

const nl = "\n"

// ============================================================================
// Pinned current behavior (green today)
// ============================================================================

/// One implicit-arg function, one test: compiles clean and the test
/// passes (the shape of /tmp/repro/ok2.tao).
pub fn single_test_implicit_fn_passes_test() {
  // let src =
  //   "type List(a) { | Cons(a, List(a)) | Nil }"
  //   <> nl
  //   <> "fn is_empty<a>(xs: List(a)) -> Bool"
  //   <> nl
  //   <> "= match xs {"
  //   <> nl
  //   <> "| Nil => True"
  //   <> nl
  //   <> "| Cons(_, _) => False"
  //   <> nl
  //   <> "}"
  //   <> nl
  //   <> ">>> is_empty(Cons(1, Nil)) False"
  // let #(errors, fails) = run(src)
  // assert errors == []
  // assert fails == []
  todo as "hangs due to result.tao hang"
}

/// A different single-test shape (three cases, /tmp/repro/ok1.tao).
pub fn single_test_is_last_passes_test() {
  let src =
    "type List(a) { | Cons(a, List(a)) | Nil }"
    <> nl
    <> "fn is_last<a>(xs: List(a)) -> Bool"
    <> nl
    <> "= match xs {"
    <> nl
    <> "| Nil => True"
    <> nl
    <> "| Cons(_, Nil) => True"
    <> nl
    <> "| Cons(_, _) => False"
    <> nl
    <> "}"
    <> nl
    <> ">>> is_last(Nil) True"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

/// A float where a `List` is expected: today no build error is reported;
/// the test simply fails at evaluation. Pinned so the refactor doesn't
/// silently change error reporting for this shape (a real type error
/// would be an improvement, but is not required).
pub fn wrong_arg_type_test_fails_test() {
  let src =
    "type List(a) { | Cons(a, List(a)) | Nil }"
    <> nl
    <> "fn is_empty<a>(xs: List(a)) -> Bool"
    <> nl
    <> "= match xs {"
    <> nl
    <> "| Nil => True"
    <> nl
    <> "| Cons(_, _) => False"
    <> nl
    <> "}"
    <> nl
    <> ">>> is_empty(1.5) True"
  let #(errors, fails) = run(src)
  assert errors == []
  assert list.length(fails) > 0
}

/// The prelude's own implicit-arg function `_or<a>` applied from a test:
/// today both tests fail at evaluation (the implicit argument never
/// resolves) with no build errors. Pinned as-is; should pass once fixed.
pub fn prelude_or_tests_fail_test() {
  let src = ">>> _or(Some(10), 20) 10" <> nl <> ">>> _or(None, 20) 20"
  let #(errors, fails) = run(src)
  assert errors == []
  assert list.length(fails) == 2
}

// ============================================================================
// Should pass when fixed (red today)
// ============================================================================

/// The prelude's `_or<a>` must actually work: both tests pass, no errors.
/// RED today (both tests fail at evaluation).
pub fn prelude_or_tests_pass_test() {
  let src = ">>> _or(Some(10), 20) 10" <> nl <> ">>> _or(None, 20) 20"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

/// Self-recursive implicit fns should compile and pass.
/// RED today (quoting on the wrong env trips the `assert index >= 0` in
/// `quote`; the implicit-arg slot leaves a stale `NVar` level).
pub fn self_recursive_implicit_fn_passes_test() {
  let src =
    "type List(a) { | Cons(a, List(a)) | Nil }"
    <> nl
    <> "fn is_empty<a>(xs: List(a)) -> Bool"
    <> nl
    <> "= match xs {"
    <> nl
    <> "| Nil => True"
    <> nl
    <> "| Cons(_, rest) => is_empty(rest)"
    <> nl
    <> "}"
    <> nl
    <> ">>> is_empty(Nil) True"
  let #(errors, fails) = run(src)
  assert errors == []
  assert fails == []
}

/// HANGS today (BAD2 minimal, /tmp/v_a.tao): two `>>>` tests on the same
/// implicit-arg function. The first test's unification leaves stale
/// implicit-binder state that makes the second test's unification loop
/// in the test phase. Must terminate (clean error or stuck tests) — a
/// hang hangs the whole suite, so the body is a `todo` until the fix
/// lands.
pub fn two_identical_tests_terminate_test() {
  // let src =
  //   "type List(a) { | Cons(a, List(a)) | Nil }"
  //   <> nl
  //   <> "fn is_empty<a>(xs: List(a)) -> Bool"
  //   <> nl
  //   <> "= match xs {"
  //   <> nl
  //   <> "| Nil => True"
  //   <> nl
  //   <> "| Cons(_, _) => False"
  //   <> nl
  //   <> "}"
  //   <> nl
  //   <> ">>> is_empty(Nil) True"
  //   <> nl
  //   <> ">>> is_empty(Nil) True"
  // let #(errors, fails) = run(src)
  // // Any non-hang outcome is acceptable: clean error or stuck tests.
  // assert True
  todo as "hangs in compile.tests: two tests of one implicit-arg function; uncomment body after fix"
}

/// HANGS today (canonical BAD2, /tmp/repro/BAD2.tao): two *different*
/// tests of the same implicit-arg function. Same fix criteria as above.
pub fn two_different_tests_terminate_test() {
  // let src =
  //   "type List(a) { | Cons(a, List(a)) | Nil }"
  //   <> nl
  //   <> "fn is_empty<a>(xs: List(a)) -> Bool"
  //   <> nl
  //   <> "= match xs {"
  //   <> nl
  //   <> "| Nil => True"
  //   <> nl
  //   <> "| Cons(_, _) => False"
  //   <> nl
  //   <> "}"
  //   <> nl
  //   <> ">>> is_empty(Nil) True"
  //   <> nl
  //   <> ">>> is_empty(Cons(1, Nil)) False"
  // let #(errors, fails) = run(src)
  // assert True
  todo as "hangs in compile.tests: BAD2 shape (two different tests); uncomment body after fix"
}

/// HANGS today: multiple implicit parameters (`fn pair<a, b>`) with two
/// tests. Same fix criteria as above.
pub fn multi_implicit_two_tests_terminate_test() {
  // let src =
  //   "fn pair<a, b>(x: a, y: b) -> a = x"
  //   <> nl
  //   <> ">>> pair(1, True) 1"
  //   <> nl
  //   <> ">>> pair(True, \"a\") True"
  // let #(errors, fails) = run(src)
  // assert True
  todo as "hangs in compile.tests: fn pair<a, b> with two tests; uncomment body after fix"
}

// ============================================================================
// Hole-solution probes (compiler invariants, no evaluation)
// ============================================================================

/// The minimal hang shape (B): 2 type params, 2 tests (see
/// /tmp/taoscratch/B_two_params_two_tests.tao).
const b_shape =
  "type Rst(value, error) {"
  <> nl
  <> "| OkX(value)"
  <> nl
  <> "| ErrX(error)"
  <> nl
  <> "}"
  <> nl
  <> "fn _orx<a, e>(r: Rst(a, e), d: a) -> a"
  <> nl
  <> "= match r {"
  <> nl
  <> "| OkX(value) => value"
  <> nl
  <> "| ErrX(_) => d"
  <> nl
  <> "}"
  <> nl
  <> ">>> _orx(OkX(10), 20) 10"
  <> nl
  <> ">>> _orx(ErrX(10), 20) 20"

/// Rigid variables (`NVar`) must never end up as hole solutions: a hole
/// "solved" with a rigid neutral is still undecidable, and retrying such a
/// substitution re-unifies stale pairs that corrupt later solutions (the
/// module-record corruption behind the result.tao hang).
pub fn b_shape_no_nevar_hole_solutions_test() {
  case compile_ctx(b_shape) {
    Some(ctx) -> {
      let has_nevar = list.any(ctx.subst, fn(entry) {
        let #(_, #(_, solution)) = entry
        case solution {
          v.Neut(v.NVar(_)) -> True
          _ -> False
        }
      })
      assert has_nevar == False
    }
    None -> panic as "parse error"
  }
}

/// A hole "solved with a module record": its solution is a record with a
/// `TypeDef` field value. Type-level records (tdef records, annotation
/// records, type records) never contain `TypeDef` values — only module
/// records do (their type-name fields). Such a solution puts a cyclic,
/// environment-capturing value into the substitution table and makes
/// later unification descend into the module record forever (the
/// result.tao hang).
fn is_module_record(value: v.Value) -> Bool {
  case value {
    v.Rcd(fields, _) ->
      list.any(fields, fn(field) {
        let #(_, #(field_val, _)) = field
        case field_val {
          v.TypeDef(..) -> True
          _ -> False
        }
      })
    _ -> False
  }
}

/// The test re-check (compile.tests) must not solve any of its own holes
/// with module records. Before the T4 fix, the B shape's tdef value holes
/// were solved with the prelude Bool module record and the user module
/// record (the frame-swap in `unwrap`'s `normalize_value` re-bound the
/// function type's stale `Var`s to module-record env slots), which made
/// the descent non-terminating (budget cutoff). The probe is scoped to
/// holes created after `compile.modules` (the main compile legitimately
/// solves dot-access row holes with module-record *fragments*; those are
/// bounded and pre-date the test phase).
///
/// The failure is a `panic`, not an `assert`: assert would display the
/// offending `Value`s, and a module record is cyclic through its captured
/// envs, so the display recurses forever and hangs the suite.
pub fn b_shape_no_module_record_test_phase_solutions_test() {
  case p.statements("scratch", b_shape) {
    Error(_) -> panic as "parse error"
    Ok(stmts) -> {
      let #(prelude, _load_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      let mods: List(Module) =
        list.append([#("scratch", stmts)], prelude)
        |> load.implicit_prelude_imports(prelude)
      let ctx =
        Context(..new_ctx, ffi: ffi.build)
        |> compile.modules(mods)
      let test_phase_start = ctx.hole_counter
      let #(_, ctx) = compile.tests(ctx, [#("scratch", stmts)])
      let bad = list.filter(ctx.subst, fn(entry) {
        let #(id, #(_, solution)) = entry
        id >= test_phase_start && is_module_record(solution)
      })
      case bad {
        [] -> Nil
        // Print only the hole IDs: a `Value` is cyclic through its
        // captured envs, so displaying it (e.g. via an `assert` failure)
        // recurses forever on a module record.
        _ -> {
          let ids =
            list.map(bad, fn(entry) { entry.0 })
            |> list.map(int.to_string)
            |> string.join(", ")
          let msg = "module-record solutions in test phase: " <> ids
          panic as msg
        }
      }
    }
  }
}

/// Module records must not carry `""`-named fields. The implicit prelude
/// import used alias `""`, so every module importing the prelude had a
/// `""` field in its record; a `""` field is positional in `pop_field`
/// and let type-level positional records (e.g. `Rst(a, e)` = `{"": a,
/// "": e}`) mis-pair with module-record fields during unification (part
/// of the result.tao hang). Implicit imports now use a reserved alias
/// that cannot be a user name. After `compile.modules` the only closed
/// records in the env are module records, so any of them with a `""`
/// field is a bug.
pub fn module_records_have_no_empty_name_fields_test() {
  case compile_ctx(b_shape) {
    Some(ctx) -> {
      let bad = list.filter(ctx.types, fn(entry) {
        let #(_, value) = entry
        case value {
          v.Rcd(fields, None) ->
            list.any(fields, fn(field) {
              let #(field_name, _) = field
              field_name == ""
            })
          _ -> False
        }
      })
      case list.length(bad) {
        0 -> Nil
        n -> {
          let msg =
            "module records with \"\" fields: " <> int.to_string(n)
          panic as msg
        }
      }
    }
    None -> panic as "parse error"
  }
}

// ============================================================================
// Harness (modeled on test/tao/overload_test.gleam)
// ============================================================================

/// Type-check an in-memory module against the prelude (as the
/// `debug-file` CLI does) and return the reported errors.
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

/// Like `check`, but returns the post-`compile.modules` context (for
/// probing compiler invariants such as hole solutions).
fn compile_ctx(source: String) -> Option(Context) {
  case p.statements("scratch", source) {
    Error(_) -> None
    Ok(stmts) -> {
      let #(prelude, _load_errors) =
        load.package_list(["lib"], [#("prelude", None)])
      let mods: List(Module) =
        list.append([#("scratch", stmts)], prelude)
        |> load.implicit_prelude_imports(prelude)
      Some(
        Context(..new_ctx, ffi: ffi.build) |> compile.modules(mods),
      )
    }
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

fn display_value(ctx: Context, value: v.Value) -> String {
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  fmt_value(ffi.build, names, value, 80, 2)
}
