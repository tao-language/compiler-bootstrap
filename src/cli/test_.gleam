import core/context.{new_ctx}
import gleam/io
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/regexp
import gleam/result
import gleam/string
import simplifile
import tao/compile
import tao/load
import tao/tests.{type TestResult}
import utils/fs

pub fn test_(root: String, paths: List(String), patterns: List(String)) -> Nil {
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
  let #(tests, ctx) = compile.tests(ctx, tests_pkg)

  // Filter tests by patterns.
  let assert Ok(pattern_re) = string.join(patterns, "|") |> regexp.from_string
  let test_defs = list.filter(tests, fn(t) { regexp.check(pattern_re, t.name) })

  // Run the tests and print the results.
  list.map(test_defs, fn(t) {
    case tests.run(ctx, t) {
      tests.TestPass(name) -> io.println("✅ " <> name)
      tests.TestFail(name, got, expr, expect) -> io.println("❌ " <> name)
      tests.TestNeutral(name, got, expr, expect) -> io.println("⚠️ " <> name)
    }
  })
  Nil
}
