/// Tests for the `tao test` test-selection logic.
import cli/test_filter.{TestSelection, filter_fn, is_selected}

// An empty selection selects every test.
pub fn empty_selection_selects_all_test() {
  let sel = TestSelection([], [], [])
  assert is_selected(sel, "path/to/file1.tao", "anything")
  assert is_selected(sel, "file1.tao", "path/to/file1.tao:3")
}

// A pattern without `:` is a test name pattern; it must match the whole
// name.
pub fn bare_pattern_matches_test_name_test() {
  let sel = TestSelection([], ["hello"], [])
  assert is_selected(sel, "path/to/file1.tao", "hello")
  assert !is_selected(sel, "path/to/file1.tao", "say_hello")
  assert !is_selected(sel, "path/to/file1.tao", "hello_world")
}

// A `--filter` pattern must match at least one of the patterns.
pub fn filter_pattern_any_match_test() {
  let sel = TestSelection([], ["hello", "world"], [])
  assert is_selected(sel, "a/f.tao", "hello")
  assert is_selected(sel, "a/f.tao", "world")
  assert !is_selected(sel, "a/f.tao", "neither")
}

// `*` matches within a path segment and never across a segment.
pub fn star_wildcard_test() {
  let sel = TestSelection([], ["infer_*"], [])
  assert is_selected(sel, "a/f.tao", "infer_1")
  assert is_selected(sel, "a/f.tao", "infer_foo_bar")
  assert !is_selected(sel, "a/f.tao", "x_infer_1")
  assert !is_selected(sel, "a/f.tao", "infer_a/b")
}

// A pattern with `:` is a module path + test name pattern; the module
// part matches any path ending with the pattern.
pub fn module_path_pattern_test() {
  let sel = TestSelection([], ["file1.tao:foo_*_bar"], [])
  assert is_selected(sel, "path/to/file1.tao", "foo_1_bar")
  assert is_selected(sel, "path/to/file1.tao", "foo_x_y_bar")
  assert !is_selected(sel, "path/to/otherfile1.tao", "foo_1_bar")
  assert !is_selected(sel, "path/to/file1.tao", "foo_x")
  assert !is_selected(sel, "path/to/file2.tao", "foo_1_bar")
}

// `**` matches across path segments.
pub fn double_star_wildcard_test() {
  let sel = TestSelection([], ["test/**:e2e_*"], [])
  assert is_selected(sel, "test/flow.tao", "e2e_checkout")
  assert is_selected(sel, "test/e2e/flow.tao", "e2e_checkout")
  assert is_selected(sel, "test/a/b/flow.tao", "e2e_x")
  assert !is_selected(sel, "src/flow.tao", "e2e_x")
  assert !is_selected(sel, "test/flow.tao", "unit_x")
}

// Tests are currently named `path/to/file.tao:LINE`, so a
// `module/path.tao:LINE` pattern targets one specific test statement,
// and a bare pattern can match just the line number.
pub fn file_line_test_names_test() {
  let sel = TestSelection([], ["file1.tao:3"], [])
  assert is_selected(sel, "path/to/file1.tao", "path/to/file1.tao:3")
  assert !is_selected(sel, "path/to/file1.tao", "path/to/file1.tao:4")
  assert !is_selected(sel, "path/to/file2.tao", "path/to/file2.tao:3")

  let sel = TestSelection([], ["3"], [])
  assert is_selected(sel, "path/to/file1.tao", "path/to/file1.tao:3")
  assert !is_selected(sel, "path/to/file1.tao", "path/to/file1.tao:42")
}

// Per-file restrictions (from `path:test1,test2` positional arguments)
// only apply to the listed file.
pub fn per_file_restriction_test() {
  let sel = TestSelection([#("path/to/file1.tao", ["my_test", "other_*"])], [], [])
  assert is_selected(sel, "path/to/file1.tao", "my_test")
  assert is_selected(sel, "path/to/file1.tao", "other_1")
  assert !is_selected(sel, "path/to/file1.tao", "something_else")
  // Files without a restriction are unrestricted.
  assert is_selected(sel, "path/to/file2.tao", "anything")
}

// A `--skip` pattern never runs, even when a filter pattern matches.
pub fn skip_wins_over_filter_test() {
  let sel = TestSelection([], ["test*"], ["test_special"])
  assert is_selected(sel, "a/f.tao", "test_normal")
  assert !is_selected(sel, "a/f.tao", "test_special")

  let sel = TestSelection([], [], ["a/f.tao:42"])
  assert is_selected(sel, "a/f.tao", "a/f.tao:1")
  assert !is_selected(sel, "a/f.tao", "a/f.tao:42")
  assert is_selected(sel, "b/f.tao", "b/f.tao:42")
}

// Skip and per-file restrictions combine.
pub fn skip_and_per_file_test() {
  let sel = TestSelection([#("a/f.tao", ["t*"])], [], ["t_skip"])
  assert is_selected(sel, "a/f.tao", "t_run")
  assert !is_selected(sel, "a/f.tao", "t_skip")
  assert !is_selected(sel, "a/f.tao", "other")
  assert is_selected(sel, "b/f.tao", "other")
}

// `filter_fn` gives the `(mod_name, test_name) -> Bool` function.
pub fn filter_fn_test() {
  let f = filter_fn(TestSelection([], ["a*"], []))
  assert f("m/x.tao", "abc")
  assert !f("m/x.tao", "bcd")
}
