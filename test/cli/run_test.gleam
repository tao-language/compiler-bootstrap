/// CLI Run Command tests
///
/// Tests for argument parsing, file loading, pipeline execution, and error handling.

import cli/run as cli
import gleeunit

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// ARGUMENT PARSING
// ============================================================================

pub fn parse_args_file_test() {
  let result = cli.parse_args(["test.core"])
  case result {
    Ok(cli.Run(cli.File("test.core"), False, False)) -> True
    _ -> False
  }
}

pub fn parse_args_inline_test() {
  let result = cli.parse_args(["-c", "42"])
  case result {
    Ok(cli.Run(cli.Inline("42"), False, False)) -> True
    _ -> False
  }
}

pub fn parse_args_help_test() {
  let result = cli.parse_args(["--help"])
  case result {
    Ok(cli.Help) -> True
    _ -> False
  }
}

pub fn parse_args_debug_test() {
  let result = cli.parse_args(["--debug", "test.core"])
  case result {
    Ok(cli.Run(cli.File("test.core"), False, True)) -> True
    _ -> False
  }
}

pub fn parse_args_too_many_after_c_test() {
  let result = cli.parse_args(["-c", "expr", "extra"])
  case result {
    Error(_) -> True
    _ -> False
  }
}

pub fn parse_args_too_many_after_debug_test() {
  let result = cli.parse_args(["--debug", "file", "extra"])
  case result {
    Error(_) -> True
    _ -> False
  }
}

pub fn parse_args_empty_test() {
  let result = cli.parse_args([])
  case result {
    Ok(cli.Help) -> True
    _ -> False
  }
}

pub fn parse_args_too_many_args_test() {
  let result = cli.parse_args(["file", "extra"])
  case result {
    Error(_) -> True
    _ -> False
  }
}

// ============================================================================
// FILE LOADING
// ============================================================================

pub fn load_file_not_found_test() {
  let result = cli.load_file("/nonexistent/path/file.core")
  case result {
    Error(msg) -> msg == "File not found: /nonexistent/path/file.core"
    _ -> False
  }
}

// ============================================================================
// PIPELINE EXECUTION
// ============================================================================

pub fn execute_inline_int_test() {
  let result = cli.execute(cli.Inline("42"))
  case result {
    Ok(_) -> True
    _ -> False
  }
}

pub fn execute_inline_string_test() {
  let result = cli.execute(cli.Inline("\"hello\""))
  case result {
    Ok(_) -> True
    _ -> False
  }
}
