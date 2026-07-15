import core/context.{new_ctx}
import core/error
import core/format
import gleam/float
import gleam/int
import gleam/io
import gleam/list
import gleam/regexp
import gleam/result
import gleam/string
import simplifile
import tao/compile
import tao/load
import tao/tests.{type TestResultSummary}
import utils/fs

pub fn test_(
  root: String,
  paths: List(String),
  patterns: List(String),
) -> TestResultSummary {
  // Load and compile the root package.
  let #(pkg, load_pkg_errors) =
    fs.list_recursive(root, string.ends_with(_, ".tao"))
    |> result.unwrap([])
    |> load.package
  let ctx = compile.package(new_ctx, pkg)

  // Load and compile the tests.
  let #(tests_pkg, load_tests_errors) =
    list.flat_map(paths, fn(path) {
      case simplifile.is_directory(path) {
        Ok(True) ->
          fs.list_recursive(path, string.ends_with(_, ".tao"))
          |> result.unwrap([])
        _ -> [path]
      }
    })
    |> load.package
  // let #(tests, ctx) = compile.tests(ctx, tests_pkg)
  let tests = compile.tests(tests_pkg)

  // Filter tests by patterns.
  let assert Ok(pattern_re) = string.join(patterns, "|") |> regexp.from_string
  let test_defs = list.filter(tests, fn(t) { regexp.check(pattern_re, t.name) })
  case list.length(test_defs) {
    1 -> io.println("Running 1 test")
    n -> io.println("Running " <> int.to_string(n) <> " tests")
  }

  // Run the tests and print the results.
  let summary = tests.run_all(ctx, test_defs)
  case summary.errors {
    [] -> Nil
    errors -> {
      let n = list.length(errors)
      let header = "------ ERRORS (" <> int.to_string(n) <> ") ------"
      io.println_error(header)
      list.map(errors, fn(err) {
        let msg = error.display_scoped(ctx.ffi, ctx.types, err)
        io.println_error(msg)
      })
      io.println_error(string.repeat("-", string.length(header)))
    }
  }
  list.map(summary.results, fn(test_result) {
    case test_result {
      // tests.TestPass(name) -> io.println("✅ " <> name)
      tests.TestPass(_name) -> Nil
      tests.TestFail(name, got, expr, expect) -> {
        let names = list.map(ctx.types, fn(entry) { entry.0 })
        io.println(
          "❌ " <> name <> ": got " <> format.value(ctx.ffi, names, got, 80, 2),
        )
      }
      tests.TestNeutral(name, got, expr, expect) -> io.println("⚠️  " <> name)
    }
  })
  io.println("")
  io.println("--- SUMMARY ---")
  let pass_percent =
    int.to_float(summary.num_pass) /. int.to_float(list.length(test_defs))
  io.println(
    "✅ "
    <> int.to_string(summary.num_pass)
    <> " passed ("
    <> float.to_string(float.to_precision(pass_percent *. 100.0, 1))
    <> "%)",
  )
  case summary.num_fail > 0 {
    True -> {
      let fail_percent =
        int.to_float(summary.num_fail) /. int.to_float(list.length(test_defs))
      io.println(
        "❌ "
        <> int.to_string(summary.num_fail)
        <> " failed ("
        <> float.to_string(float.to_precision(fail_percent *. 100.0, 1))
        <> "%)",
      )
    }
    False -> Nil
  }
  case summary.num_neutral > 0 {
    True ->
      io.println(
        "⚠️  " <> int.to_string(summary.num_neutral) <> " could not be evaluated",
      )
    False -> Nil
  }
  summary
}
