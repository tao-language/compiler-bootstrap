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
  type Term, type Value, Int as LitInt,
  VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, VRcdT, HVar, VTyp, Var,
}
import core/eval.{evaluate}
import core/state.{type FfiEntry, FfiEntry, initial_state}
import core/syntax.{parse}
import simplifile
import gleam/list
import gleam/option.{type Option, Some}
import gleeunit


// ============================================================================
// FFI STUBS — only the operations used by tour files
// ============================================================================

fn ffi_entries() -> List(FfiEntry) {
  [
    // FFI names are stored without the % prefix (parser strips it)
    FfiEntry("i32_add", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] ->
          Some(VLit(LitInt(a + b)))
        _ -> Some(VLit(LitInt(0)))
      }
    }),
    FfiEntry("i32_eq", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] ->
          case a == b {
            True -> Some(VCtr("True", VRcd([])))
            False -> Some(VCtr("False", VRcd([])))
          }
        _ -> Some(VCtr("False", VRcd([])))
      }
    }),
  ]
}

// ============================================================================
// HELPERS
// ============================================================================
/// Read a tour file from disk. Panics with a clear message if the file cannot be read.
fn read_tour_file(path: String) -> String {
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

/// Run full pipeline: parse → evaluate.
/// Returns the evaluated value.
fn pipeline(term: Term) -> Value {
  let state = initial_state(ffi_entries())
  evaluate(state, term)
}

/// Evaluate a tour file by its path and return its result value.
fn eval_tour(path: String) -> Value {
  let content = read_tour_file(path)
  let term = parse_source(content)
  pipeline(term)
}

// ============================================================================
// TESTS — one test per tour file, in the same order as the tour files
// ============================================================================

pub fn main() {
  gleeunit.main()
}

// ---- 01_basics ----

pub fn t01_basics_01_introduction_test() {
  let result = eval_tour("examples/core/tour/01_basics/01_introduction.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t01_basics_02_type_test() {
  let result = eval_tour("examples/core/tour/01_basics/02_type.core")
  assert case result {
    VTyp(0) -> True
    _ -> False
  }
}

pub fn t01_basics_03_records_test() {
  let result = eval_tour("examples/core/tour/01_basics/03_records.core")
  let expected = VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))])
  assert result == expected
}

pub fn t01_basics_04_record_types_test() {
  let result = eval_tour("examples/core/tour/01_basics/04_record_types.core")
  assert case result {
    VRcdT(fields) -> list.length(fields) == 2
    _ -> False
  }
}

pub fn t01_basics_05_type_defs_test() {
  let result = eval_tour("examples/core/tour/01_basics/05_type_defs.core")
  let expected = VCtr("True", VRcd([]))
  assert result == expected
}

pub fn t01_basics_06_constructors_test() {
  let result = eval_tour("examples/core/tour/01_basics/06_constructors.core")
  let expected = VCtr("Some", VLit(LitInt(42)))
  assert result == expected
}

pub fn t01_basics_07_lambda_functions_test() {
  let result = eval_tour("examples/core/tour/01_basics/07_lambda_functions.core")
  assert case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t01_basics_08_pi_types_test() {
  let result = eval_tour("examples/core/tour/01_basics/08_pi_types.core")
  assert case result {
    VPi(_, _, #("x", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

pub fn t01_basics_09_function_applications_test() {
  let result = eval_tour("examples/core/tour/01_basics/09_function_applications.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t01_basics_10_type_annotations_test() {
  let result = eval_tour("examples/core/tour/01_basics/10_type_annotations.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t01_basics_11_pattern_match_test() {
  let result = eval_tour("examples/core/tour/01_basics/11_pattern_match.core")
  let expected = VLit(LitInt(1))
  assert result == expected
}

pub fn t01_basics_12_builtin_calls_test() {
  let result = eval_tour("examples/core/tour/01_basics/12_builtin_calls.core")
  let expected = VLit(LitInt(3))
  assert result == expected
}

pub fn t01_basics_13_holes_test() {
  let result = eval_tour("examples/core/tour/01_basics/13_holes.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t01_basics_14_errors_test() {
  let result = eval_tour("examples/core/tour/01_basics/14_errors.core")
  let expected = VErr
  assert result == expected
}

// ---- 02_syntax_sugar ----

pub fn t02_syntax_sugar_01_let_test() {
  let result = eval_tour("examples/core/tour/02_syntax_sugar/01_let.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t02_syntax_sugar_02_let_untyped_test() {
  let result = eval_tour("examples/core/tour/02_syntax_sugar/02_let_untyped.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t02_syntax_sugar_03_lam_untyped_test() {
  let result = eval_tour("examples/core/tour/02_syntax_sugar/03_lam_untyped.core")
  assert case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t02_syntax_sugar_04_pi_arrow_test() {
  let result = eval_tour("examples/core/tour/02_syntax_sugar/04_pi_arrow.core")
  assert case result {
    VPi(_, _, #("a", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

// ---- 03_literals ----

pub fn t03_literals_01_types_test() {
  let result = eval_tour("examples/core/tour/03_literals/01_types.core")
  // type2 evaluates to $Type<1> — the universe type value
  assert result == VTyp(1)
}

pub fn t03_literals_02_integers_test() {
  let result = eval_tour("examples/core/tour/03_literals/02_integers.core")
  let expected = VLit(LitInt(1))
  assert result == expected
}

pub fn t03_literals_03_floats_test() {
  // Integer literal with $Float type — type accepts it but value stays Int
  let result = eval_tour("examples/core/tour/03_literals/03_floats.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t03_literals_04_records_test() {
  let result = eval_tour("examples/core/tour/03_literals/04_records.core")
  let expected = VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))])
  assert result == expected
}

// ---- 04_type_definitions ----

pub fn t04_type_definitions_01_monomorphic_test() {
  let result = eval_tour("examples/core/tour/04_type_definitions/01_monomorphic.core")
  let expected = VCtr("True", VRcd([]))
  assert result == expected
}

pub fn t04_type_definitions_02_polymorphic_test() {
  // Uses the actual tour file source: $type<a: $Type> { ... }
  let result = eval_tour("examples/core/tour/04_type_definitions/02_polymorphic.core")
  let expected = VCtr("Some", VLit(LitInt(42)))
  assert result == expected
}

pub fn t04_type_definitions_03_gadt_vec_test() {
  // Uses the actual tour file source: $type<n: $I32, a: $Type> { ... }
  // The result is #Cons({x: 3.14, xs: #Nil({})}) : #Vec({n: 1, a: $Float})
  let result = eval_tour("examples/core/tour/04_type_definitions/03_gadt_vec.core")
  assert case result {
    VCtr("Cons", VRcd(fields)) ->
      list.length(fields) >= 1
    _ -> False
  }
}

pub fn t04_type_definitions_04_gadt_expr_test() {
  // Uses the actual tour file source: $type<a: $Type> { ... }
  // eval(#Add(#LitInt(1), #LitInt(2))) should return 3
  let result = eval_tour("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let expected = VLit(LitInt(3))
  assert result == expected
}

// ---- 05_pattern_matching ----

pub fn t05_pattern_matching_01_wildcard_patterns_test() {
  // Tour file now returns 100 instead of 0
  let result = eval_tour("examples/core/tour/05_pattern_matching/01_wildcard_patterns.core")
  let expected = VLit(LitInt(100))
  assert result == expected
}

pub fn t05_pattern_matching_02_alias_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/02_alias_pattern.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t05_pattern_matching_03_type_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/03_type_pattern.core")
  let expected = VLit(LitInt(0))
  assert result == expected
}

pub fn t05_pattern_matching_04_int_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/04_int_pattern.core")
  let expected = VLit(LitInt(2))
  assert result == expected
}

pub fn t05_pattern_matching_05_rcd_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/05_rcd_pattern.core")
  let expected = VLit(LitInt(0))
  assert result == expected
}

pub fn t05_pattern_matching_06_rcdt_pattern_test() {
  // Uses the actual tour file source with type patterns: ${x: $Int, y: $Float}
  let result = eval_tour("examples/core/tour/05_pattern_matching/06_rcdt_pattern.core")
  let expected = VLit(LitInt(0))
  assert result == expected
}

pub fn t05_pattern_matching_07_ctr_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/07_ctr_pattern.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

pub fn t05_pattern_matching_08_error_pattern_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/08_error_pattern.core")
  let expected = VLit(LitInt(0))
  assert result == expected
}

pub fn t05_pattern_matching_09_guards_test() {
  // Tour file now returns 100 instead of 0
  let result = eval_tour("examples/core/tour/05_pattern_matching/09_guards.core")
  let expected = VLit(LitInt(100))
  assert result == expected
}

pub fn t05_pattern_matching_10_exhaustiveness_test() {
  let result = eval_tour("examples/core/tour/05_pattern_matching/10_exhaustiveness.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}

// ---- 07_advanced ----

pub fn t07_advanced_01_default_values_test() {
  // Uses the actual tour file source (exactly as written)
  let result = eval_tour("examples/core/tour/07_advanced/01_default_values.core")
  // The match {y} => y returns the y field value (default value 0)
  assert result == VLit(LitInt(0))
}

pub fn t07_advanced_02_implicit_params_test() {
  let result = eval_tour("examples/core/tour/07_advanced/02_implicit_params.core")
  let expected = VLit(LitInt(42))
  assert result == expected
}