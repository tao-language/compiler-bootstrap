/// Tests for the CLI path expansion (files and directories, recursive
/// `.tao` lookup).
import cli/common.{expand_paths}
import gleam/list
import gleam/result
import gleam/string

pub fn expand_paths_directory_test() {
  let result =
    expand_paths(["test/cli/data"])
    |> result.map(list.sort(_, string.compare))
  assert result
    == Ok([
      "test/cli/data/f1.tao",
      "test/cli/data/sub/f2.tao",
    ])
}

pub fn expand_paths_file_test() {
  assert expand_paths(["test/cli/data/f1.tao"]) == Ok(["test/cli/data/f1.tao"])
}

pub fn expand_paths_normalizes_dot_slash_test() {
  assert expand_paths(["./test/cli/data/f1.tao"])
    == Ok(["test/cli/data/f1.tao"])
}

pub fn expand_paths_missing_path_test() {
  let result = expand_paths(["test/cli/data/missing.tao"])
  assert case result {
    Error(msg) -> string.contains(msg, "missing.tao")
    _ -> False
  }
}

pub fn expand_paths_deduplicates_test() {
  let result =
    expand_paths(["test/cli/data", "test/cli/data/f1.tao"])
    |> result.map(list.sort(_, string.compare))
  assert result
    == Ok([
      "test/cli/data/f1.tao",
      "test/cli/data/sub/f2.tao",
    ])
}
