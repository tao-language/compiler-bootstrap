/// `tao test [paths..]` — load the given `.tao` files (and the
/// prelude), type-check them, then run the files' `>>>` tests (the
/// prelude's own tests are not run), filtered by the selection. Prints
/// the test results and a summary to stdout; exits with status 1 when
/// there are build errors or any test fails, 0 otherwise.
import cli/common
import cli/test_filter.{TestSelection, filter_fn}
import core/context
import gleam/int
import gleam/io
import gleam/list
import gleam/string
import simplifile
import tao/ast.{type Module} as tao
import tao/compile
import tao/tests

/// The parsed arguments of `tao test`: the files to run tests for, any
/// per-file test name restrictions, and the `--filter`/`--skip` patterns.
pub type TestArgs {
  TestArgs(
    /// The file and directory paths (positional arguments).
    paths: List(String),
    /// Per-file test name restrictions (`path:test1,test2`).
    per_file: List(#(String, List(String))),
    /// The `--filter` patterns.
    filter: List(String),
    /// The `--skip` patterns.
    skip: List(String),
  )
}

/// Parse the arguments after `tao test`: positional paths (optionally
/// `path:test1,test2`) plus repeatable `--filter`/`--skip` flags (either
/// `--flag pattern` or `--flag=pattern`).
pub fn parse_test_args(args: List(String)) -> Result(TestArgs, String) {
  parse(args, [], [], [], [])
}

fn parse(
  args: List(String),
  paths: List(String),
  per_file: List(#(String, List(String))),
  filter: List(String),
  skip: List(String),
) -> Result(TestArgs, String) {
  case args {
    [] -> Ok(TestArgs(paths, per_file, filter, skip))
    ["--filter", pattern, ..rest] ->
      parse(rest, paths, per_file, [pattern, ..filter], skip)
    ["--filter=" <> pattern, ..rest] ->
      parse(rest, paths, per_file, [pattern, ..filter], skip)
    ["--skip", pattern, ..rest] ->
      parse(rest, paths, per_file, filter, [pattern, ..skip])
    ["--skip=" <> pattern, ..rest] ->
      parse(rest, paths, per_file, filter, [pattern, ..skip])
    ["--filter"] -> Error("missing pattern for --filter")
    ["--skip"] -> Error("missing pattern for --skip")
    [arg, ..rest] -> {
      // A positional argument is a path, optionally followed by `:test1,test2`
      // to restrict the tests run in that file.
      case string.split_once(arg, ":") {
        Ok(#(path, names)) -> {
          let path = common.normalize(path)
          let per_file = list.append(per_file, [#(path, test_names(names))])
          parse(rest, list.append(paths, [path]), per_file, filter, skip)
        }
        Error(Nil) -> parse(rest, list.append(paths, [arg]), per_file, filter, skip)
      }
    }
  }
}

fn test_names(names: String) -> List(String) {
  list.filter_map(string.split(names, ","), fn(name) {
    case string.length(name) {
      0 -> Error(Nil)
      _ -> Ok(name)
    }
  })
}

pub fn run_tests(args: TestArgs) -> Nil {
  // Test names can only be restricted for files, not directories.
  let bad_file =
    list.find(args.per_file, fn(entry) {
      let #(path, _) = entry
      case simplifile.is_file(path) {
        Ok(True) -> False
        _ -> True
      }
    })
  case bad_file {
    Ok(#(path, _)) -> {
      io.println_error("error: test names can only be given for a file: " <> path)
      common.exit(1)
    }
    Error(Nil) -> run_loaded(args)
  }
}

fn run_loaded(args: TestArgs) -> Nil {
  case common.load(args.paths) {
    Error(msg) -> {
      io.println_error("error: " <> msg)
      common.exit(1)
    }
    Ok(loaded) ->
      case list.length(loaded.errors) {
        0 -> {
          let ctx = common.compile(loaded.mods, loaded.prelude)
          common.print_build_errors(ctx)
          case ctx.errors {
            [] -> run_tests_(loaded, ctx, args)
            _ -> common.exit(1)
          }
        }
        _ -> {
          common.print_syntax_errors(loaded.errors)
          common.exit(1)
        }
      }
  }
}

fn run_tests_(
  loaded: common.Loaded,
  ctx: context.Context,
  args: TestArgs,
) -> Nil {
  // Compile the tests of the input files only (not the prelude's).
  let #(test_defs, ctx) = compile.tests(ctx, loaded.mods)

  // Pair every test with the file it was loaded from, then keep only the
  // selected ones.
  let all_tests = pair_modules(loaded.paths, loaded.mods, test_defs)
  let sel = TestSelection(args.per_file, args.filter, args.skip)
  let filter = filter_fn(sel)
  let selected =
    list.filter(all_tests, fn(t) { filter(t.0, t.1) })

  case list.length(selected) {
    1 -> io.println("Running 1 test")
    n -> io.println("Running " <> int.to_string(n) <> " tests")
  }

  let defs = list.map(selected, fn(t) { t.2 })
  let summary = tests.run_all(ctx, defs)

  list.map(summary.results, fn(res) {
    case res {
      tests.TestPass(name) -> io.println("✓ " <> strip_name(name))
      tests.TestFail(name, got, _, _) -> {
        io.println("✗ " <> strip_name(name))
        io.println("  got: " <> common.fmt_value(ctx, got))
      }
      tests.TestNeutral(name, got, _, _) -> {
        io.println("? " <> strip_name(name))
        io.println("  got: " <> common.fmt_value(ctx, got))
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

/// Attach the file path of each test. `compile.tests` returns the tests
/// in module order, and statement order within a module, so the tests
/// can be split back up by counting each module's test statements.
fn pair_modules(
  paths: List(String),
  mods: List(Module),
  test_defs: List(tests.TestDef),
) -> List(#(String, String, tests.TestDef)) {
  case paths, mods {
    [path, ..paths], [#(_, stmts), ..mods] -> {
      let n = list.count(stmts, fn(stmt) {
        case stmt.data {
          tao.Test(..) -> True
          _ -> False
        }
      })
      let #(head, tail) = list.split(test_defs, n)
      let pairs =
        list.map(head, fn(def) { #(path, strip_name(def.name), def) })
      list.append(pairs, pair_modules(paths, mods, tail))
    }
    _, [] -> []
    [], _ -> []
  }
}

/// Strip the `">>> "` prefix the parser puts on test names.
fn strip_name(name: String) -> String {
  case name {
    ">>> " <> rest -> rest
    _ -> name
  }
}
