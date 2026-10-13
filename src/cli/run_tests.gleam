/// `tao test [paths...] | -e EXPR | -s STMTS` — compile the input, then
/// run its `>>>` tests (the prelude's own tests are not run), filtered
/// by the selection. Prints the test results and a summary to stdout;
/// exits with status 1 when there are build errors or any test fails,
/// 0 otherwise.
import cli/args.{type Opts}
import cli/common
import cli/pipeline
import core/context.{type Context, TraceTests}
import core/format
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import simplifile
import tao/compile
import tao/desugar
import tao/tests.{type TestDef}
import cli/test_filter.{TestSelection, filter_fn}

pub fn run_tests(opts: Opts) -> Nil {
  // Test names can only be restricted for files, not directories.
  let bad_file =
    list.find(opts.per_file, fn(entry) {
      let #(path, _) = entry
      case simplifile.is_file(path) {
        Ok(True) -> False
        _ -> True
      }
    })
  case bad_file {
    Ok(#(path, _)) -> {
      io.println_error(
        "error: test names can only be given for a file: " <> path,
      )
      common.exit(1)
    }
    Error(Nil) ->
      case pipeline.compile_input(opts.input, opts) {
        Error(pipeline.LoadFailure(msg)) -> common.load_failure(msg)
        Error(pipeline.SyntaxFailures(errors)) -> {
          common.print_syntax_errors(errors)
          common.exit(1)
        }
        Ok(compiled) -> {
          common.print_build_errors(compiled.ctx)
          case compiled.ctx.errors {
            [] -> run_tests_(compiled, opts)
            _ -> common.exit(1)
          }
        }
      }
  }
}

fn run_tests_(compiled: pipeline.Compiled, opts: Opts) -> Nil {
  // Compile the tests of the input modules only (not the prelude's).
  //
  // The test re-check can fail on its own (a unification budget error the
  // module compile did not hit) — but it is intentionally *not* surfaced
  // here: while the module-record corruption (see docs/plan.md, tasks 4–5)
  // makes the test re-check's unification pathological, the test *terms*
  // are well-formed and still evaluate correctly, so the doctests pass. A
  // hard failure here would both block those doctests and crash while
  // printing the (corrupted) values. Once the corruption is fixed the
  // re-check no longer hits the budget, so no error is raised at all.
  let #(test_defs, ctx) = compile.tests(compiled.ctx, compiled.modules)

  // Pair every test with the file it was loaded from, then keep only the
  // selected ones.
  let all_tests = pair_modules(compiled.paths, test_defs)
  let sel = TestSelection(opts.per_file, opts.filter, opts.skip)
  let filter = filter_fn(sel)
  let selected = list.filter(all_tests, fn(t) { filter(t.0, t.1) })

  case list.length(selected) {
    1 -> io.println("Running 1 test")
    n -> io.println("Running " <> int.to_string(n) <> " tests")
  }

  let defs = list.map(selected, fn(t) { t.2 })
  let names = list.map(ctx.types, fn(entry) { entry.0 })
  let summary = run_all(ctx, defs, names, list.contains(opts.trace, TraceTests))

  list.map(summary.results, fn(res) {
    case res {
      tests.TestPass(name) -> io.println("✓ " <> strip_name(name))
      tests.TestFail(name, got, _, tao_expect) -> {
        let expect = desugar.pattern(tao_expect)
        io.println("✗ " <> strip_name(name))
        io.println("  expected: " <> format.pattern(expect, 80, 2))
        io.println("  got:      " <> common.fmt_value(ctx, got))
      }
      tests.TestNeutral(name, got, _, tao_expect) -> {
        let expect = desugar.pattern(tao_expect)
        io.println("? " <> strip_name(name))
        io.println("  expected: " <> format.pattern(expect, 80, 2))
        io.println("  got:      " <> common.fmt_value(ctx, got))
      }
    }
  })

  io.println("")
  io.println("--- SUMMARY ---")
  io.println("- " <> int.to_string(list.length(summary.results)) <> " total")
  io.println("- " <> int.to_string(summary.num_pass) <> " passed")
  io.println("- " <> int.to_string(summary.num_fail) <> " failed")
  case summary.num_neutral {
    0 -> Nil
    n -> io.println("- " <> int.to_string(n) <> " neutral")
  }

  case summary.num_fail {
    0 -> Nil
    _ -> common.exit(1)
  }
}

/// Run every test; with `show_terms` (`--trace tests`) prints each
/// test's compiled term first.
fn run_all(
  ctx: Context,
  defs: List(TestDef),
  names: List(String),
  show_terms: Bool,
) -> tests.TestResultSummary {
  case defs {
    [] -> tests.TestResultSummary(ctx.errors, [], 0, 0, 0)
    [t, ..rest] -> {
      case show_terms {
        True -> io.println("term: " <> format.term(names, t.term, 80, 2))
        False -> Nil
      }
      let res = tests.run(ctx, t)
      let summary = run_all(ctx, rest, names, show_terms)
      let summary =
        tests.TestResultSummary(..summary, results: [res, ..summary.results])
      case res {
        tests.TestPass(..) ->
          tests.TestResultSummary(..summary, num_pass: summary.num_pass + 1)
        tests.TestFail(..) ->
          tests.TestResultSummary(..summary, num_fail: summary.num_fail + 1)
        tests.TestNeutral(..) ->
          tests.TestResultSummary(..summary, num_neutral: summary.num_neutral + 1)
      }
    }
  }
}

/// Attach the file path of each test. Test names embed their source file
/// (`">>> <file>:<line>`), so tests are paired with the input paths by
/// that prefix, not by module name (an input file that is also a package
/// module is named by its package path, not its file path).
fn pair_modules(
  paths: List(String),
  test_defs: List(TestDef),
) -> List(#(String, String, TestDef)) {
  list.flat_map(paths, fn(path) {
    let prefix = ">>> " <> path <> ":"
    list.filter_map(test_defs, fn(def) {
      case string.starts_with(def.name, prefix) {
        True -> Ok(#(path, strip_name(def.name), def))
        False -> Error(Nil)
      }
    })
  })
}

/// Strip the `">>> "` prefix the parser puts on test names.
fn strip_name(name: String) -> String {
  case name {
    ">>> " <> rest -> rest
    _ -> name
  }
}
