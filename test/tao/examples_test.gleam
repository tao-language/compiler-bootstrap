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
import gleam/option.{None, Some, type Option}
import gleam/string
import tao/ast.{Pattern, PAny, PCtr, PLit, PRcd, PTuple, PVar, type Pattern}
import tao/compile
import tao/load
import tao/tests.{
  TestFail,
  TestNeutral,
  TestPass,
  run_all,
  type TestResultSummary,
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

/// Build the message for a failing `num_fail == 0` assert: a summary
/// line plus, for every failed (and neutral) test, its name and the
/// expected vs actual values, so the assert failure is self-contained
/// (like the `tao test` CLI output) without re-running via the CLI.
fn test_failures_message(ctx: Context, summary: TestResultSummary) -> String {
  let details = list.filter_map(summary.results, fn(res) {
    case res {
      TestFail(name, got, _, expect) -> Ok([
        "  ✗ " <> strip_name(name),
        "    expected: " <> fmt_pattern(expect),
        "    got:      " <> common.fmt_value(ctx, got),
      ])
      TestNeutral(name, got, _, _) -> Ok([
        "  ? " <> strip_name(name) <> " (could not be fully evaluated)",
        "    got: " <> common.fmt_value(ctx, got),
      ])
      TestPass(..) -> Error(Nil)
    }
  })
  ["Test run: "
    <> int.to_string(summary.num_pass) <> " passed, "
    <> int.to_string(summary.num_fail) <> " failed, "
    <> int.to_string(summary.num_neutral) <> " neutral:"]
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
    PTuple(args) ->
      "(" <> string.join(list.map(args, fmt_pattern), ", ") <> ")"
    PRcd(fields, tail) -> {
      let fields = list.map(fields, fn(field) {
        let #(name, pat) = field
        name <> ": " <> fmt_pattern(pat)
      })
      "{" <> string.join(fields, ", ") <> fmt_tail(tail) <> "}"
    }
    PCtr(tag, args, tail) -> {
      let args = list.map(args, fn(arg) {
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
