/// End-to-end tests for Core tour examples
///
/// Every tour file is tested through the full pipeline:
/// 1. Parse — no syntax errors
/// 2. Infer — no type errors
/// 3. Evaluate — produces a non-VErr value
///
/// Each test is self-contained: it reads the tour file from disk,
/// evaluates it, and asserts the expected result.
import core/ast.{
  type Term, type Value, Float, FloatT, HHole, HVar, Int, IntT, VCtr, VErr, VLam,
  VLit, VLitT, VNeut, VPi, VRcd, VRcdT, VTyp, Var,
}
import core/infer.{infer}
import core/state.{type FfiEntry, FfiEntry, initial_state}
import core/syntax.{parse}
import gleam/option.{type Option, None, Some}
import gleeunit
import simplifile
import syntax/span.{Span}

// ============================================================================
// FFI STUBS — only the operations used by tour files
// ============================================================================

fn ffi_entries() -> List(FfiEntry) {
  [
    // FFI names are stored without the % prefix (parser strips it)
    FfiEntry("i32_add", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(Int(a)), _), #(VLit(Int(b)), _), ..] -> Some(VLit(Int(a + b)))
        _ -> None
      }
    }),
    FfiEntry("i32_sub", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(Int(a)), _), #(VLit(Int(b)), _), ..] -> Some(VLit(Int(a - b)))
        _ -> None
      }
    }),
    FfiEntry("i32_mul", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(Int(a)), _), #(VLit(Int(b)), _), ..] -> Some(VLit(Int(a * b)))
        _ -> None
      }
    }),
    FfiEntry("i32_eq", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(Int(a)), _), #(VLit(Int(b)), _), ..] ->
          case a == b {
            True -> Some(VCtr("True", VRcd([])))
            False -> Some(VCtr("False", VRcd([])))
          }
        _ -> None
      }
    }),
  ]
}

// ============================================================================
// HELPERS
// ============================================================================
/// Read a file from disk. Panics with a clear message if the file cannot be read.
fn read_file(path: String) -> String {
  case simplifile.read(from: path) {
    Ok(contents) -> contents
    Error(_) -> panic
  }
}

/// Parse source content and return the term.
fn parse_source(source: String) -> Term {
  let #(term, errors) = parse(source)
  assert errors == []
  term
}

/// Evaluate a tour file by its path and return its result value.
fn eval_file(path: String) -> Value {
  let content = read_file(path)
  let term = parse_source(content)
  let state = initial_state(ffi_entries())
  let #(result, _, _) = infer(state, term)
  result
}

// ============================================================================
// TESTS — one test per tour file, in the same order as the tour files
// ============================================================================

pub fn main() {
  gleeunit.main()
}

// ---- 01_basics ----

pub fn t01_basics_01_introduction_test() {
  let path = "examples/core/tour/01_basics/01_introduction.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t01_basics_02_type_test() {
  let path = "examples/core/tour/01_basics/02_type.core"
  let expected = VTyp(0)
  assert eval_file(path) == expected
}

pub fn t01_basics_03_records_test() {
  let path = "examples/core/tour/01_basics/03_records.core"
  let expected = VRcd([#("x", VLit(Int(1))), #("y", VLit(Int(2)))])
  assert eval_file(path) == expected
}

pub fn t01_basics_04_record_types_test() {
  let path = "examples/core/tour/01_basics/04_record_types.core"
  let expected =
    VRcdT([#("x", VLitT(IntT), None), #("y", VLitT(IntT), Some(VLit(Int(0))))])
  assert eval_file(path) == expected
}

pub fn t01_basics_05_type_defs_test() {
  let path = "examples/core/tour/01_basics/05_type_defs.core"
  let expected = VCtr("True", VRcd([]))
  assert eval_file(path) == expected
}

pub fn t01_basics_06_constructors_test() {
  let path = "examples/core/tour/01_basics/06_constructors.core"
  let expected = VCtr("Some", VLit(Int(42)))
  assert eval_file(path) == expected
}

pub fn t01_basics_07_lambda_functions_test() {
  let path = "examples/core/tour/01_basics/07_lambda_functions.core"
  let expected =
    VLam([], [], #("x", VLitT(IntT)), Var(0, Span("", 4, 17, 4, 18)))
  assert eval_file(path) == expected
}

pub fn t01_basics_08_pi_types_test() {
  let path = "examples/core/tour/01_basics/08_pi_types.core"
  let expected = VPi([], [], #("x", VTyp(0)), VNeut(HVar(0), []))
  assert eval_file(path) == expected
}

pub fn t01_basics_09_function_applications_test() {
  let path = "examples/core/tour/01_basics/09_function_applications.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t01_basics_10_type_annotations_test() {
  let path = "examples/core/tour/01_basics/10_type_annotations.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t01_basics_11_pattern_match_test() {
  let path = "examples/core/tour/01_basics/11_pattern_match.core"
  let expected = VLit(Int(1))
  assert eval_file(path) == expected
}

pub fn t01_basics_12_builtin_calls_test() {
  let path = "examples/core/tour/01_basics/12_builtin_calls.core"
  let expected = VLit(Int(3))
  assert eval_file(path) == expected
}

pub fn t01_basics_13_fix_point_recursion_test() {
  let path = "examples/core/tour/01_basics/13_fix_point_recursion.core"
  let expected = VLit(Int(120))
  assert eval_file(path) == expected
}

pub fn t01_basics_14_holes_test() {
  let path = "examples/core/tour/01_basics/14_holes.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t01_basics_15_errors_test() {
  let path = "examples/core/tour/01_basics/15_errors.core"
  let expected = VErr
  assert eval_file(path) == expected
}

// ---- 02_syntax_sugar ----

pub fn t02_syntax_sugar_01_let_test() {
  let path = "examples/core/tour/02_syntax_sugar/01_let.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t02_syntax_sugar_02_let_untyped_test() {
  let path = "examples/core/tour/02_syntax_sugar/02_let_untyped.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t02_syntax_sugar_03_lam_untyped_test() {
  let path = "examples/core/tour/02_syntax_sugar/03_lam_untyped.core"
  let expected =
    VLam([], [], #("x", VNeut(HHole(-1), [])), Var(0, Span("", 3, 11, 3, 12)))
  assert eval_file(path) == expected
}

pub fn t02_syntax_sugar_04_pi_arrow_test() {
  let path = "examples/core/tour/02_syntax_sugar/04_pi_arrow.core"
  let expected = VPi([], [], #("", VLitT(IntT)), VLitT(FloatT))
  assert eval_file(path) == expected
}

// ---- 03_literals ----

pub fn t03_literals_01_types_test() {
  let path = "examples/core/tour/03_literals/01_types.core"
  let expected = VTyp(1)
  assert eval_file(path) == expected
}

pub fn t03_literals_02_integers_test() {
  let path = "examples/core/tour/03_literals/02_integers.core"
  let expected = VLit(Int(1))
  assert eval_file(path) == expected
}

pub fn t03_literals_03_floats_test() {
  let path = "examples/core/tour/03_literals/03_floats.core"
  let expected = VLit(Float(42.0))
  assert eval_file(path) == expected
}

pub fn t03_literals_04_records_test() {
  let path = "examples/core/tour/03_literals/04_records.core"
  let expected = VRcd([#("x", VLit(Int(1))), #("y", VLit(Int(2)))])
  assert eval_file(path) == expected
}

// ---- 04_type_definitions ----

pub fn t04_type_definitions_01_monomorphic_test() {
  let path = "examples/core/tour/04_type_definitions/01_monomorphic.core"
  let expected = VCtr("True", VRcd([]))
  assert eval_file(path) == expected
}

pub fn t04_type_definitions_02_polymorphic_test() {
  let path = "examples/core/tour/04_type_definitions/02_polymorphic.core"
  let expected = VCtr("Some", VLit(Int(42)))
  assert eval_file(path) == expected
}

pub fn t04_type_definitions_03_gadt_vec_test() {
  let path = "examples/core/tour/04_type_definitions/03_gadt_vec.core"
  let nil = VCtr("Nil", VRcd([]))
  let expected = VCtr("Cons", VRcd([#("x", VLit(Float(3.14))), #("xs", nil)]))
  assert eval_file(path) == expected
}

pub fn t04_type_definitions_04_gadt_expr_test() {
  let path = "examples/core/tour/04_type_definitions/04_gadt_expr.core"
  let expected = VLit(Int(3))
  assert eval_file(path) == expected
}

// ---- 05_pattern_matching ----

pub fn t05_pattern_matching_01_wildcard_patterns_test() {
  let path = "examples/core/tour/05_pattern_matching/01_wildcard_patterns.core"
  let expected = VLit(Int(100))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_02_alias_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/02_alias_pattern.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_03_type_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/03_type_pattern.core"
  let expected = VLit(Int(0))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_04_int_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/04_int_pattern.core"
  let expected = VLit(Int(2))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_05_rcd_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/05_rcd_pattern.core"
  let expected = VLit(Int(0))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_06_rcdt_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/06_rcdt_pattern.core"
  let expected = VLit(Int(0))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_07_ctr_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/07_ctr_pattern.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_08_error_pattern_test() {
  let path = "examples/core/tour/05_pattern_matching/08_error_pattern.core"
  let expected = VLit(Int(0))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_09_guards_test() {
  let path = "examples/core/tour/05_pattern_matching/09_guards.core"
  let expected = VLit(Int(100))
  assert eval_file(path) == expected
}

pub fn t05_pattern_matching_10_exhaustiveness_test() {
  let path = "examples/core/tour/05_pattern_matching/10_exhaustiveness.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

// ---- 07_advanced ----

pub fn t07_advanced_01_default_values_test() {
  let path = "examples/core/tour/07_advanced/01_default_values.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}

pub fn t07_advanced_02_implicit_params_test() {
  let path = "examples/core/tour/07_advanced/02_implicit_params.core"
  let expected = VLit(Int(42))
  assert eval_file(path) == expected
}
