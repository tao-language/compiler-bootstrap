/// End-to-end tests for the CLI pipeline (`cli/pipeline`): inline `-e`/`-s`
/// inputs go through the same parse/compile path as files, with the
/// prelude loaded.
import cli/args.{type Input, type Opts, InputExpr, InputFiles, InputStmts, Opts}
import cli/pipeline
import core/context
import core/literals as lit
import core/value as v
import gleam/list
import gleam/option.{type Option, None, Some}
import tao/compile
import tao/tests

fn opts(input: Input) -> Opts {
  Opts(
    input: input,
    trace: [],
    paths: [],
    packages: [],
    dump_def: None,
    filter: [],
    skip: [],
    per_file: [],
  )
}

/// The value of a top-level definition in the first input module.
fn mod_value(compiled: pipeline.Compiled, name: String) -> Option(v.Value) {
  case compiled.modules {
    [#(mod_name, _), ..] ->
      case context.lookup_var(compiled.ctx, mod_name) {
        Some(#(v.Rcd(values, _), _)) ->
          case list.key_find(values, name) {
            Ok(#(value, _)) -> Some(value)
            Error(Nil) -> None
          }
        _ -> None
      }
    [] -> None
  }
}

fn is_int(opt: Option(v.Value), expected: Int) -> Bool {
  case opt {
    Some(v.Lit(lit.Int(x))) -> x == expected
    _ -> False
  }
}

/// `-e` wraps the expression in `let __result = <expr>` and evaluates it.
pub fn pipeline_expr_test() {
  let input = InputExpr("1 + 1")
  case pipeline.compile_input(input, opts(input)) {
    Ok(compiled) -> {
      assert compiled.ctx.errors == []
      assert is_int(mod_value(compiled, pipeline.expr_result_name), 2)
    }
    Error(_) -> panic as "compile_input failed"
  }
}

/// `-s` accepts `;`-separated statements, like a file.
pub fn pipeline_stmts_semicolon_test() {
  let input = InputStmts("let x = 1; let y = 2")
  case pipeline.compile_input(input, opts(input)) {
    Ok(compiled) -> {
      assert compiled.ctx.errors == []
      assert is_int(mod_value(compiled, "x"), 1)
      assert is_int(mod_value(compiled, "y"), 2)
    }
    Error(_) -> panic as "compile_input failed"
  }
}

/// `-s` with `>>>` tests: the tests compile and run against the inline
/// module (labels flow into the test names).
pub fn pipeline_stmts_tests_test() {
  let input = InputStmts("let x = 1\n>>> x 1")
  case pipeline.compile_input(input, opts(input)) {
    Ok(compiled) -> {
      assert compiled.ctx.errors == []
      let #(test_defs, ctx) = compile.tests(compiled.ctx, compiled.modules)
      assert list.length(test_defs) == 1
      let res = case test_defs {
        [t, ..] -> tests.run(ctx, t)
        _ -> panic as "no test"
      }
      assert case res {
        tests.TestPass(..) -> True
        _ -> False
      }
    }
    Error(_) -> panic as "compile_input failed"
  }
}

/// A parse error in inline input is a pipeline failure (no printing).
pub fn pipeline_expr_parse_error_test() {
  let input = InputExpr("let x =")
  case pipeline.compile_input(input, opts(input)) {
    Ok(_) -> panic as "expected a parse error"
    Error(pipeline.SyntaxFailures(errors)) -> {
      assert list.length(errors) == 1
      Nil
    }
    Error(pipeline.LoadFailure(_)) -> panic as "expected a syntax failure"
  }
}

/// File input still works through the same pipeline.
pub fn pipeline_file_test() {
  let input = InputFiles(["test/cli/data/f1.tao"])
  case pipeline.compile_input(input, opts(input)) {
    Ok(compiled) -> {
      assert compiled.ctx.errors == []
      assert compiled.paths == ["test/cli/data/f1.tao"]
    }
    Error(_) -> panic as "compile_input failed"
  }
}
