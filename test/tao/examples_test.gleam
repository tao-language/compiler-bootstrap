/// Corpus validation: compile the whole example corpus (the gallery
/// modules plus the prelude package, exactly as the `debug-file` CLI
/// loads them) through the full pipeline and run every `>>> test`
/// statement. This is the in-repo regression for the prelude/overload
/// machinery: the overloaded operators' dependent dispatches leave
/// deferred constraints (e.g. `NVar ~ Rcd`) that must *not* become
/// errors at resolve time, and every prelude test must still evaluate.
import cli/common
import core/context.{type Context, Context, new_ctx}
import core/ffi
import core/literals as lit
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import syntax/span.{Span}
import tao/ast.{
  type Pattern, type Stmt, PAny, PCtr, PLit, PRcd, PTuple, PVar, Pattern,
  Import, int, let_var,
}
import tao/compile
import tao/declare
import tao/load
import tao/tests.{
  type TestResultSummary, TestFail, TestNeutral, TestPass, run_all,
}

pub fn examples_prelude_test() {
  let #(prelude, e) = load.package_list(["lib"], [#("prelude", None)])
  assert e == []
  assert list.length(prelude) >= 1
  let mods = prelude
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  assert ctx.errors == []
  let #(test_defs, ctx) = compile.tests(ctx, prelude)
  assert list.length(test_defs) >= 1
  let summary = run_all(ctx, test_defs)
  let failures = test_failures_message(ctx, summary)
  assert summary.num_fail == 0 as failures
}

pub fn examples_gallery_test() {
  let #(gallery, e1) = load.directory("examples/tao/gallery")
  let #(prelude, e2) = load.package_list(["lib"], [#("prelude", None)])
  assert e1 == []
  assert e2 == []
  assert list.length(gallery) >= 1
  assert list.length(prelude) >= 1
  let mods =
    list.append(gallery, prelude)
    |> load.implicit_prelude_imports(prelude)
  let ctx =
    Context(..new_ctx, ffi: ffi.build)
    |> compile.modules(mods)
  assert ctx.errors == []
  let #(test_defs, ctx) = compile.tests(ctx, gallery)
  assert list.length(test_defs) >= 1
  let summary = run_all(ctx, test_defs)
  let failures = test_failures_message(ctx, summary)
  assert summary.num_fail == 0 as failures
}

/// Pin the resolution of the global `_or` collision. The prelude's
/// `bool`, `option`, and `result` modules all export an internal `_or`,
/// and the implicit prelude import flattens all three into every
/// non-prelude module's global scope. Name resolution takes the *first*
/// matching entry in a module's definition list, so the winner is whichever
/// prelude module is imported first. Sorting the prelude modules by name
/// makes that deterministic: `/prelude/bool` sorts first, so `bool._or`
/// is the `_or` a lookup finds. (A `_or(True, True)` type-check is not a
/// reliable pin — the prelude overloads leave deferred constraints that
/// are silently accepted, so it type-checks under several `_or`s.)
pub fn prelude_or_collision_deterministic_test() {
  let #(prelude, e) = load.package_list(["lib"], [#("prelude", None)])
  assert e == []
  let s = Span("or_collision", 0, 0, 0, 0)
  let scratch = #("/scratch", [let_var("x", None, int(1, s), s)])
  let all = list.append(prelude, [scratch])
  let with_imports = load.implicit_prelude_imports(all, load.prelude_modules(all))
  let #(defs, _) = declare.modules(with_imports)
  let or_path = import_path_for(defs, "/scratch", "_or")
  let msg = "expected bool._or to win the global _or, got: " <> or_path
  assert or_path == "/prelude/bool" as msg
}

/// The module path that `name` in `mod`'s definition list resolves to
/// (the import it was flattened from), or `""` if it is not an import.
fn import_path_for(
  defs: List(#(String, List(#(String, Stmt)))),
  mod: String,
  name: String,
) -> String {
  case list.key_find(defs, mod) {
    Ok(mod_defs) ->
      case list.key_find(mod_defs, name) {
        Ok(stmt) ->
          case stmt.data {
            Import(path, _, _) -> path
            _ -> ""
          }
        Error(Nil) -> ""
      }
    Error(Nil) -> ""
  }
}

/// Build the message for a failing `num_fail == 0` assert: a summary
/// line plus, for every failed (and neutral) test, its name and the
/// expected vs actual values, so the assert failure is self-contained
/// (like the `tao test` CLI output) without re-running via the CLI.
fn test_failures_message(ctx: Context, summary: TestResultSummary) -> String {
  let details =
    list.filter_map(summary.results, fn(res) {
      case res {
        TestFail(name, got, _, expect) ->
          Ok([
            "  ✗ " <> strip_name(name),
            "    expected: " <> fmt_pattern(expect),
            "    got:      " <> common.fmt_value(ctx, got),
          ])
        TestNeutral(name, got, _, _) ->
          Ok([
            "  ? " <> strip_name(name) <> " (could not be fully evaluated)",
            "    got: " <> common.fmt_value(ctx, got),
          ])
        TestPass(..) -> Error(Nil)
      }
    })
  [
    "Test run: "
    <> int.to_string(summary.num_pass)
    <> " passed, "
    <> int.to_string(summary.num_fail)
    <> " failed, "
    <> int.to_string(summary.num_neutral)
    <> " neutral:",
  ]
  |> list.append(list.flatten(details))
  |> string.join("\n")
}

/// Strip the `">>> "` prefix the parser puts on test names.
fn strip_name(name: String) -> String {
  case name {
    ">>> " <> rest -> rest
    _ -> name
  }
}

/// Format a Tao pattern for display. (The `core/format` printer only
/// covers the Core AST; this is a minimal stand-in for test messages.)
fn fmt_pattern(p: Pattern) -> String {
  case p.data {
    PAny -> "_"
    PVar(name) -> name
    PLit(value) ->
      case value {
        lit.Int(n) -> int.to_string(n)
        lit.Float(f) -> float.to_string(f)
      }
    PTuple(args) -> "(" <> string.join(list.map(args, fmt_pattern), ", ") <> ")"
    PRcd(fields, tail) -> {
      let fields =
        list.map(fields, fn(field) {
          let #(name, pat) = field
          name <> ": " <> fmt_pattern(pat)
        })
      "{" <> string.join(fields, ", ") <> fmt_tail(tail) <> "}"
    }
    PCtr(tag, args, tail) -> {
      let args =
        list.map(args, fn(arg) {
          let #(name, pat) = arg
          case name {
            // An empty name is a positional argument: print the value only.
            "" -> fmt_pattern(pat)
            _ -> name <> ": " <> fmt_pattern(pat)
          }
        })
      "#" <> tag <> "(" <> string.join(args, ", ") <> fmt_tail(tail) <> ")"
    }
  }
}

fn fmt_tail(opt_tail: Option(Pattern)) -> String {
  case opt_tail {
    None -> ""
    Some(Pattern(PAny, _)) -> ", .."
    Some(t) -> ", .." <> fmt_pattern(t)
  }
}
