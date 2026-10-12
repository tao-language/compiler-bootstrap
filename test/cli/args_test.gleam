/// Tests for the shared CLI argument parser (`cli/args`).
import cli/args.{InputExpr, InputFiles, InputStmts, parse}
import core/context.{TraceHoles, TraceParse}
import gleam/option.{None, Some}
import gleam/string

/// The parsed `-e` input.
pub fn parse_expr_flag_test() {
  assert case parse("run", ["-e", "1 + 1"]) {
    Ok(opts) -> opts.input == InputExpr("1 + 1")
    _ -> False
  }
}

pub fn parse_expr_long_flag_test() {
  assert case parse("check", ["--expr", "x"]) {
    Ok(opts) -> opts.input == InputExpr("x")
    _ -> False
  }
}

pub fn parse_stmt_flag_test() {
  assert case parse("run", ["-s", "let x = 1"]) {
    Ok(opts) -> opts.input == InputStmts("let x = 1")
    _ -> False
  }
}

pub fn parse_stmt_long_flag_test() {
  assert case parse("test", ["--stmt", "let x = 1"]) {
    Ok(opts) -> opts.input == InputStmts("let x = 1")
    _ -> False
  }
}

pub fn parse_files_test() {
  assert case parse("check", ["a.tao", "b.tao"]) {
    Ok(opts) -> opts.input == InputFiles(["a.tao", "b.tao"])
    _ -> False
  }
}

pub fn parse_default_input_is_files_test() {
  assert case parse("check", []) {
    Ok(opts) -> opts.input == InputFiles([])
    _ -> False
  }
}

pub fn parse_mix_files_and_expr_error_test() {
  assert case parse("run", ["a.tao", "-e", "1"]) {
    Error(msg) -> string.contains(msg, "mix")
    _ -> False
  }
}

pub fn parse_mix_expr_and_stmt_error_test() {
  assert case parse("run", ["-e", "1", "-s", "let x = 1"]) {
    Error(msg) -> string.contains(msg, "combine")
    _ -> False
  }
}

pub fn parse_two_exprs_error_test() {
  assert case parse("run", ["-e", "1", "-e", "2"]) {
    Error(msg) -> string.contains(msg, "combine")
    _ -> False
  }
}

pub fn parse_trace_kinds_test() {
  assert case parse("run", ["-e", "1", "--trace", "parse", "--trace=holes"]) {
    Ok(opts) -> opts.trace == [TraceParse, TraceHoles]
    _ -> False
  }
}

pub fn parse_unknown_trace_kind_error_test() {
  assert case parse("run", ["--trace", "wibbles"]) {
    Error(msg) -> string.contains(msg, "unknown trace kind")
    _ -> False
  }
}

pub fn parse_path_and_add_test() {
  assert case parse("run", ["--path", "pkg", "--add", "foo:1.0.0", "--add=bar"]) {
    Ok(opts) ->
      opts.paths == ["pkg"]
      && opts.packages == [#("foo", Some("1.0.0")), #("bar", None)]
    _ -> False
  }
}

pub fn parse_dump_def_test() {
  assert case parse("run", ["--dump-def", "f"]) {
    Ok(opts) -> opts.dump_def == Some("f")
    _ -> False
  }
}

pub fn parse_dump_def_equals_test() {
  assert case parse("run", ["--dump-def=f"]) {
    Ok(opts) -> opts.dump_def == Some("f")
    _ -> False
  }
}

pub fn parse_filter_on_check_error_test() {
  assert case parse("check", ["--filter", "foo"]) {
    Error(msg) -> string.contains(msg, "only supported by test")
    _ -> False
  }
}

pub fn parse_filter_on_test_test() {
  assert case parse("test", ["--filter", "foo", "--skip", "bar"]) {
    Ok(opts) -> opts.filter == ["foo"] && opts.skip == ["bar"]
    _ -> False
  }
}

pub fn parse_filter_missing_value_error_test() {
  assert case parse("test", ["--filter"]) {
    Error(msg) -> string.contains(msg, "missing pattern")
    _ -> False
  }
}

pub fn parse_per_file_test_names_test() {
  assert case parse("test", ["a.tao:t1,t2", "b.tao"]) {
    Ok(opts) ->
      opts.input == InputFiles(["a.tao", "b.tao"])
      && opts.per_file == [#("a.tao", ["t1", "t2"])]
    _ -> False
  }
}

pub fn parse_per_file_normalizes_dot_slash_test() {
  assert case parse("test", ["./a.tao:t1"]) {
    Ok(opts) -> opts.per_file == [#("a.tao", ["t1"])]
    _ -> False
  }
}

pub fn parse_unknown_flag_error_test() {
  assert case parse("run", ["--frobnicate"]) {
    Error(msg) -> string.contains(msg, "unknown flag")
    _ -> False
  }
}

pub fn parse_missing_flag_value_error_test() {
  assert case parse("run", ["-e"]) {
    Error(_) -> True
    _ -> False
  }
}
