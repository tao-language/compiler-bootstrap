/// Test selection for `tao test`.
///
/// A pattern is either a test name, `test_name`, or a module path with a
/// test name, `module/path.tao:test_name`. Both parts support glob
/// wildcards: `*` matches any run of characters within a path segment
/// and `**` matches across segments. A module path pattern matches any
/// path that *ends* with the pattern (so `file1.tao` matches
/// `path/to/file1.tao`); a test name pattern must match the whole test
/// name.
import gleam/list
import gleam/regexp
import gleam/string
import utils/glob.{glob_to_regex}

/// The tests to run, as built up from the `tao test` command line.
pub type TestSelection {
  TestSelection(
    /// Per-file test name restrictions, from positional arguments of the
    /// form `path:test1,test2`; files not listed are unrestricted.
    per_file: List(#(String, List(String))),
    /// `--filter` patterns: only tests matching at least one are run
    /// (all tests, when empty).
    filter: List(String),
    /// `--skip` patterns: matching tests are never run, even if a filter
    /// pattern matches.
    skip: List(String),
  )
}

/// Whether the test `(mod_name, test_name)` is selected: it must match a
/// `--filter` pattern (when any), the per-file restriction of its file
/// (when there is one), and no `--skip` pattern.
///
/// `mod_name` is the test's file path (e.g. `"path/to/file1.tao"`) and
/// `test_name` its name (e.g. `"path/to/file1.tao:3"` or `"my_test"`).
pub fn is_selected(
  sel: TestSelection,
  mod_name: String,
  test_name: String,
) -> Bool {
  let name = name_part(mod_name, test_name)
  case list.any(
    sel.skip,
    fn(p) { pattern_matches(p, mod_name, test_name, name) },
  ) {
    True -> False
    False -> {
      let filtered =
        case sel.filter {
          [] -> True
          _ -> list.any(
            sel.filter,
            fn(p) { pattern_matches(p, mod_name, test_name, name) },
          )
        }
      let per_file_ok =
        case list.key_find(sel.per_file, mod_name) {
          Error(Nil) -> True
          Ok(names) -> list.any(
            names,
            fn(p) { anchored_glob(p, name) || anchored_glob(p, test_name) },
          )
        }
      filtered && per_file_ok
    }
  }
}

/// The `(mod_name, test_name) -> Bool` filter function to apply to the
/// tests.
pub fn filter_fn(sel: TestSelection) -> fn(String, String) -> Bool {
  fn(mod_name, test_name) { is_selected(sel, mod_name, test_name) }
}

/// A pattern matches a test when its module part (when the pattern
/// contains a `:`) matches the file path and its name part (always
/// present) matches the test name.
fn pattern_matches(
  pattern: String,
  mod_name: String,
  test_name: String,
  name: String,
) -> Bool {
  case string.split_once(pattern, ":") {
    Ok(#(mod, name_pat)) ->
      mod_glob(mod, mod_name)
        && { anchored_glob(name_pat, test_name) || anchored_glob(name_pat, name) }
    Error(Nil) -> anchored_glob(pattern, test_name) || anchored_glob(pattern, name)
  }
}

/// The test name without its module path prefix: tests are currently
/// named `path/to/file.tao:LINE`, so a name pattern can also match just
/// the `LINE` part (and a test's own name, when it has one).
fn name_part(mod_name: String, test_name: String) -> String {
  let prefix = mod_name <> ":"
  case string.starts_with(test_name, prefix) {
    True -> string.drop_start(test_name, string.length(prefix))
    False -> test_name
  }
}

/// A module path pattern matches any path ending with the pattern, on a
/// path-segment boundary (`file1.tao` matches `path/to/file1.tao` but
/// not `path/to/otherfile1.tao`).
fn mod_glob(pattern: String, path: String) -> Bool {
  let assert Ok(re) = regexp.from_string("(^|/)" <> glob_to_regex(pattern) <> "$")
  regexp.check(re, path)
}

/// A test name pattern must match the whole name.
fn anchored_glob(pattern: String, name: String) -> Bool {
  let assert Ok(re) = regexp.from_string("^" <> glob_to_regex(pattern) <> "$")
  regexp.check(re, name)
}
