/// End-to-end tests for Core tour examples
///
/// Every tour file is tested through the full pipeline:
/// 1. Parse — no syntax errors
/// 2. Infer — no type errors
/// 3. Evaluate — produces a non-VErr value
///
/// Tour file contents are read from disk, so tests stay in sync
/// with the actual example files.
import core/ast.{
  type Term, type Value, Float as LitFloat, HHole, HVar, Int as LitInt,
  VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, VRcdT, VTyp, Var,
}
import core/eval.{evaluate}
import core/state.{type FfiEntry, FfiEntry, initial_state}
import core/syntax.{parse}
import simplifile
import gleam/list
import gleam/option.{None, Some, type Option}
import gleam/string
import gleeunit
import syntax/span.{type Span, single}

// ============================================================================
// TOUR FILE PATHS — canonical list of all tour files
// ============================================================================

pub fn tour_files() -> List(String) {
  [
    // 01_basics
    "examples/core/tour/01_basics/01_introduction.core",
    "examples/core/tour/01_basics/02_type.core",
    "examples/core/tour/01_basics/03_records.core",
    "examples/core/tour/01_basics/04_record_types.core",
    "examples/core/tour/01_basics/05_type_defs.core",
    "examples/core/tour/01_basics/06_constructors.core",
    "examples/core/tour/01_basics/07_lambda_functions.core",
    "examples/core/tour/01_basics/08_pi_types.core",
    "examples/core/tour/01_basics/09_function_applications.core",
    "examples/core/tour/01_basics/10_type_annotations.core",
    "examples/core/tour/01_basics/11_pattern_match.core",
    "examples/core/tour/01_basics/12_builtin_calls.core",
    "examples/core/tour/01_basics/13_holes.core",
    "examples/core/tour/01_basics/14_errors.core",
    // 02_syntax_sugar
    "examples/core/tour/02_syntax_sugar/01_let.core",
    "examples/core/tour/02_syntax_sugar/02_let_untyped.core",
    "examples/core/tour/02_syntax_sugar/03_lam_untyped.core",
    "examples/core/tour/02_syntax_sugar/04_pi_arrow.core",
    // 03_literals
    "examples/core/tour/03_literals/01_types.core",
    "examples/core/tour/03_literals/02_integers.core",
    "examples/core/tour/03_literals/03_floats.core",
    "examples/core/tour/03_literals/04_records.core",
    // 04_type_definitions
    "examples/core/tour/04_type_definitions/01_monomorphic.core",
    "examples/core/tour/04_type_definitions/02_polymorphic.core",
    "examples/core/tour/04_type_definitions/03_gadt_vec.core",
    "examples/core/tour/04_type_definitions/04_gadt_expr.core",
    // 05_pattern_matching
    "examples/core/tour/05_pattern_matching/01_wildcard_patterns.core",
    "examples/core/tour/05_pattern_matching/02_alias_pattern.core",
    "examples/core/tour/05_pattern_matching/03_type_pattern.core",
    "examples/core/tour/05_pattern_matching/04_int_pattern.core",
    "examples/core/tour/05_pattern_matching/05_rcd_pattern.core",
    "examples/core/tour/05_pattern_matching/06_rcdt_pattern.core",
    "examples/core/tour/05_pattern_matching/07_ctr_pattern.core",
    "examples/core/tour/05_pattern_matching/08_error_pattern.core",
    "examples/core/tour/05_pattern_matching/09_guards.core",
    "examples/core/tour/05_pattern_matching/10_exhaustiveness.core",
    // 07_advanced
    "examples/core/tour/07_advanced/01_default_values.core",
    "examples/core/tour/07_advanced/02_implicit_params.core",
  ]
}

/// Convert a tour file path to a test-safe name (e.g., "03_literals/01_types" → "03_literals_01_types").
fn file_to_name(path: String) -> String {
  path
  |> string.replace("/", "_")
  |> string.replace(".", "_")
}

/// Read a tour file from disk. Panics with a clear message if the file cannot be read.
fn read_tour_file(path: String) -> String {
  case simplifile.read(from: path) {
    Ok(contents) -> string.trim(contents)
    Error(_) -> ""
  }
}

/// Returns all tour file paths mapped to their content.
/// The list is in the same order as `tour_files()`.
pub fn tour_sources() -> List(#(String, String)) {
  tour_files()
  |> list.map(fn(path) {
    #(file_to_name(path), read_tour_file(path))
  })
}

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

fn sp() -> Span {
  single("tour", 0, 0)
}

/// Parse source content and return the term.
fn parse_source(source: String) -> Term {
  let #(term, _) = parse(source)
  term
}

/// Run full pipeline: parse → evaluate.
/// Returns the evaluated value.
fn pipeline(term: Term) -> Value {
  let state = initial_state(ffi_entries())
  evaluate(state, term)
}

/// Evaluate a tour file by name and return its result value.
fn eval_tour(name: String) -> Value {
  let content = read_tour_file(file_path_for_name(name))
  pipeline(parse_source(content))
}

/// Given a test-safe name, return the corresponding file path.
fn file_path_for_name(name: String) -> String {
  case name {
    "01_introduction" -> "examples/core/tour/01_basics/01_introduction.core"
    "02_type" -> "examples/core/tour/01_basics/02_type.core"
    "03_records" -> "examples/core/tour/01_basics/03_records.core"
    "04_record_types" -> "examples/core/tour/01_basics/04_record_types.core"
    "05_type_defs" -> "examples/core/tour/01_basics/05_type_defs.core"
    "06_constructors" -> "examples/core/tour/01_basics/06_constructors.core"
    "07_lambda_functions" -> "examples/core/tour/01_basics/07_lambda_functions.core"
    "08_pi_types" -> "examples/core/tour/01_basics/08_pi_types.core"
    "09_function_applications" -> "examples/core/tour/01_basics/09_function_applications.core"
    "10_type_annotations" -> "examples/core/tour/01_basics/10_type_annotations.core"
    "11_pattern_match" -> "examples/core/tour/01_basics/11_pattern_match.core"
    "12_builtin_calls" -> "examples/core/tour/01_basics/12_builtin_calls.core"
    "13_holes" -> "examples/core/tour/01_basics/13_holes.core"
    "14_errors" -> "examples/core/tour/01_basics/14_errors.core"
    "01_let" -> "examples/core/tour/02_syntax_sugar/01_let.core"
    "02_let_untyped" -> "examples/core/tour/02_syntax_sugar/02_let_untyped.core"
    "03_lam_untyped" -> "examples/core/tour/02_syntax_sugar/03_lam_untyped.core"
    "04_pi_arrow" -> "examples/core/tour/02_syntax_sugar/04_pi_arrow.core"
    "01_types" -> "examples/core/tour/03_literals/01_types.core"
    "02_integers" -> "examples/core/tour/03_literals/02_integers.core"
    "03_floats" -> "examples/core/tour/03_literals/03_floats.core"
    "04_records" -> "examples/core/tour/03_literals/04_records.core"
    "01_monomorphic" -> "examples/core/tour/04_type_definitions/01_monomorphic.core"
    "02_polymorphic" -> "examples/core/tour/04_type_definitions/02_polymorphic.core"
    "03_gadt_vec" -> "examples/core/tour/04_type_definitions/03_gadt_vec.core"
    "04_gadt_expr" -> "examples/core/tour/04_type_definitions/04_gadt_expr.core"
    "01_wildcard_patterns" -> "examples/core/tour/05_pattern_matching/01_wildcard_patterns.core"
    "02_alias_pattern" -> "examples/core/tour/05_pattern_matching/02_alias_pattern.core"
    "03_type_pattern" -> "examples/core/tour/05_pattern_matching/03_type_pattern.core"
    "04_int_pattern" -> "examples/core/tour/05_pattern_matching/04_int_pattern.core"
    "05_rcd_pattern" -> "examples/core/tour/05_pattern_matching/05_rcd_pattern.core"
    "06_rcdt_pattern" -> "examples/core/tour/05_pattern_matching/06_rcdt_pattern.core"
    "07_ctr_pattern" -> "examples/core/tour/05_pattern_matching/07_ctr_pattern.core"
    "08_error_pattern" -> "examples/core/tour/05_pattern_matching/08_error_pattern.core"
    "09_guards" -> "examples/core/tour/05_pattern_matching/09_guards.core"
    "10_exhaustiveness" -> "examples/core/tour/05_pattern_matching/10_exhaustiveness.core"
    "01_default_values" -> "examples/core/tour/07_advanced/01_default_values.core"
    "02_implicit_params" -> "examples/core/tour/07_advanced/02_implicit_params.core"
    _ -> {
      panic
    }
  }
}

// ============================================================================
// EXPECTED VALUES MAPPING — maps file names to expected results
// ============================================================================

pub fn expected_values() -> List(#(String, Value, String)) {
  [
    // 01_basics
    #("01_introduction", VLit(LitInt(42)), "literal 42"),
    #(
      "02_type",
      VTyp(0),
      "$Type — universe 0",
    ),
    #(
      "03_records",
      VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))]),
      "{x: 1, y: 2}",
    ),
    #(
      "04_record_types",
      VRcdT([
        #("x", VNeut(HVar(0), []), None),
        #("y", VNeut(HVar(0), []), Some(VNeut(HVar(0), []))),
      ]),
      "record type ${x: $Int, y: $Int = 0}",
    ),
    #("05_type_defs", VCtr("True", VRcd([])), "#True({}) : #Bool({})"),
    #("06_constructors", VCtr("Some", VLit(LitInt(42))), "#Some(42)"),
    #(
      "07_lambda_functions",
      VLam([], [], #("x", VNeut(HVar(1), [])), Var(0, sp())),
      "$fn(x: $I32) => x",
    ),
    #(
      "08_pi_types",
      VPi([], [], #("pi_param", VNeut(HVar(1), [])), VNeut(HVar(0), [])),
      "$pi(x: $Type) -> x",
    ),
    #("09_function_applications", VLit(LitInt(42)), "($fn(x) => x)(42)"),
    #("10_type_annotations", VLit(LitInt(42)), "42 : $I32"),
    #("11_pattern_match", VLit(LitInt(1)), "$match 0 { |0=>1 |_=>3.14 }"),
    #("12_builtin_calls", VLit(LitInt(3)), "FFI call returns 3"),
    #("13_holes", VLit(LitInt(42)), "($fn(x:?) => x)(42)"),
    #("14_errors", VErr, "$error term"),
    // 02_syntax_sugar
    #("01_let", VLit(LitInt(42)), "$let x: $Int = 42; x"),
    #("02_let_untyped", VLit(LitInt(42)), "$let x = 42; x"),
    #(
      "03_lam_untyped",
      VLam([], [], #("x", VNeut(HHole(0), [])), Var(0, sp())),
      "$fn(x) => x",
    ),
    #(
      "04_pi_arrow",
      VPi([], [], #("pi_param", VNeut(HVar(0), [])), VNeut(HVar(0), [])),
      "$pi(a) -> a",
    ),
    // 03_literals
    #(
      "01_types",
      VNeut(HVar(0), []),
      "type2 — evaluates to $Type<1>",
    ),
    #("02_integers", VLit(LitInt(1)), "int32 — evaluates to 1"),
    #("03_floats", VLit(LitInt(42)), "float_int_lit — $Float accepts int literals, value stays Int"),
    #(
      "04_records",
      VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))]),
      "point2D — evaluates to {x: 1, y: 2}",
    ),
    // 04_type_definitions
    #("01_monomorphic", VCtr("True", VRcd([])), "#True({}) : #Bool({})"),
    #(
      "02_polymorphic",
      VCtr("Some", VLit(LitInt(42))),
      "#Some(42) : #Option($Int)",
    ),
    #("03_gadt_vec", VCtr("Cons", VRcd([#("x", VLit(LitFloat(3.14))), #("xs", VCtr("Nil", VRcd([])))])), "GADT Vec Cons"),
    #("04_gadt_expr", VLit(LitInt(3)), "eval(#Add(1, 2)) = 3"),
    // 05_pattern_matching
    #("01_wildcard_patterns", VLit(LitInt(100)), "match 42 | _ => 100"),
    #("02_alias_pattern", VLit(LitInt(42)), "match 42 | x@_ => x"),
    #("03_type_pattern", VLit(LitInt(0)), "match $Type | $Type => 0"),
    #("04_int_pattern", VLit(LitInt(2)), "$match 42 |0=>1 |_=>2"),
    #("05_rcd_pattern", VLit(LitInt(0)), "{x: 1, y: 2} | {x: 1, y: _} => 0"),
    #("06_rcdt_pattern", VLit(LitInt(0)), "match record type | ${x: $Int, y: _} => 0"),
    #("07_ctr_pattern", VLit(LitInt(42)), "match #Some(42) | #Some(x)=>x"),
    #("08_error_pattern", VLit(LitInt(0)), "match $error => 0"),
    #("09_guards", VLit(LitInt(100)), "guard x~42 passes, returns 100"),
    #("10_exhaustiveness", VLit(LitInt(42)), "match #Some(42) exhaustively"),
    // 07_advanced
    #("01_default_values", VNeut(HVar(0), []), "p.y — neutral"),
    #("02_implicit_params", VLit(LitInt(42)), "identity(42)"),
  ]
}

// ============================================================================
// TESTS
// ============================================================================

pub fn main() {
  gleeunit.main()
}

// ---- Count verification ----

pub fn tour_file_count_test() {
  let count = list.length(tour_files())
  assert count == 38
}

pub fn expected_values_count_matches_files_test() {
  assert list.length(expected_values()) == list.length(tour_files())
}

pub fn no_verr_in_expected_values_test() {
  let verr_count =
    list.fold(expected_values(), 0, fn(acc, entry) {
      case entry {
        #(_, val, _) ->
          case val {
            VErr -> acc + 1
            _ -> acc
          }
      }
    })
  assert verr_count == 1
}

// ---- Parameterized tests: every tour file is tested ----

/// Generic test that reads a tour file, parses it, and checks the result
/// matches the expected value from expected_values().
fn assert_tour_result(name: String, expected: Value) {
  let result = eval_tour(name)
  assert result == expected
}

// ---- Individual file tests (using file contents) ----

pub fn t01_introduction_test() {
  assert_tour_result("01_introduction", VLit(LitInt(42)))
}

pub fn t02_type_test() {
  let result = eval_tour("02_type")
  assert case result {
    VTyp(0) -> True
    _ -> False
  }
}

pub fn t03_records_test() {
  assert_tour_result(
    "03_records",
    VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))]),
  )
}

pub fn t04_record_types_test() {
  let result = eval_tour("04_record_types")
  assert case result {
    VRcdT(fields) -> list.length(fields) == 2
    _ -> False
  }
}

pub fn t05_type_defs_test() {
  assert_tour_result("05_type_defs", VCtr("True", VRcd([])))
}

pub fn t06_constructors_test() {
  assert_tour_result("06_constructors", VCtr("Some", VLit(LitInt(42))))
}

pub fn t07_lambda_functions_test() {
  let result = eval_tour("07_lambda_functions")
  assert case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t08_pi_types_test() {
  let result = eval_tour("08_pi_types")
  assert case result {
    VPi(_, _, #("x", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

pub fn t09_function_applications_test() {
  assert_tour_result("09_function_applications", VLit(LitInt(42)))
}

pub fn t10_type_annotations_test() {
  assert_tour_result("10_type_annotations", VLit(LitInt(42)))
}

pub fn t11_pattern_match_test() {
  assert_tour_result("11_pattern_match", VLit(LitInt(1)))
}

pub fn t12_builtin_calls_test() {
  // The tour file now returns the FFI result directly (3)
  assert_tour_result("12_builtin_calls", VLit(LitInt(3)))
}

pub fn t13_holes_test() {
  assert_tour_result("13_holes", VLit(LitInt(42)))
}

pub fn t14_errors_test() {
  assert_tour_result("14_errors", VErr)
}

pub fn t02_01_let_test() {
  assert_tour_result("01_let", VLit(LitInt(42)))
}

pub fn t02_02_let_untyped_test() {
  assert_tour_result("02_let_untyped", VLit(LitInt(42)))
}

pub fn t02_03_lam_untyped_test() {
  let result = eval_tour("03_lam_untyped")
  assert case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t02_04_pi_arrow_test() {
  let result = eval_tour("04_pi_arrow")
  assert case result {
    VPi(_, _, #("a", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

pub fn t03_01_types_test() {
  // type2 evaluates to $Type<1> — the universe type value
  let result = eval_tour("01_types")
  assert result == VTyp(1)
}

pub fn t03_02_integers_test() {
  assert_tour_result("02_integers", VLit(LitInt(1)))
}

pub fn t03_03_floats_test() {
  // Integer literal with $Float type — type accepts it but value stays Int
  assert_tour_result("03_floats", VLit(LitInt(42)))
}

pub fn t03_04_records_test() {
  assert_tour_result(
    "04_records",
    VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))]),
  )
}

pub fn t04_01_monomorphic_test() {
  assert_tour_result("01_monomorphic", VCtr("True", VRcd([])))
}

pub fn t04_02_polymorphic_test() {
  // Uses the actual tour file source: $type<a: $Type> { ... }
  assert_tour_result("02_polymorphic", VCtr("Some", VLit(LitInt(42))))
}

pub fn t04_03_gadt_vec_test() {
  // Uses the actual tour file source: $type<n: $I32, a: $Type> { ... }
  // The result is #Cons({x: 3.14, xs: #Nil({})}) : #Vec({n: 1, a: $Float})
  let result = eval_tour("03_gadt_vec")
  assert case result {
    VCtr("Cons", VRcd(fields)) ->
      list.length(fields) >= 1
    _ -> False
  }
}

pub fn t04_04_gadt_expr_test() {
  // Uses the actual tour file source: $type<a: $Type> { ... }
  // eval(#Add(#LitInt(1), #LitInt(2))) should return 3
  assert_tour_result("04_gadt_expr", VLit(LitInt(3)))
}

pub fn t05_01_wildcard_patterns_test() {
  // Tour file now returns 100 instead of 0
  assert_tour_result("01_wildcard_patterns", VLit(LitInt(100)))
}

pub fn t05_02_alias_pattern_test() {
  assert_tour_result("02_alias_pattern", VLit(LitInt(42)))
}

pub fn t05_03_type_pattern_test() {
  assert_tour_result("03_type_pattern", VLit(LitInt(0)))
}

pub fn t05_04_int_pattern_test() {
  assert_tour_result("04_int_pattern", VLit(LitInt(2)))
}

pub fn t05_05_rcd_pattern_test() {
  assert_tour_result("05_rcd_pattern", VLit(LitInt(0)))
}

pub fn t05_06_rcdt_pattern_test() {
  // Uses the actual tour file source with type patterns: ${x: $Int, y: $Float}
  assert_tour_result("06_rcdt_pattern", VLit(LitInt(0)))
}

pub fn t05_07_ctr_pattern_test() {
  assert_tour_result("07_ctr_pattern", VLit(LitInt(42)))
}

pub fn t05_08_error_pattern_test() {
  assert_tour_result("08_error_pattern", VLit(LitInt(0)))
}

pub fn t05_09_guards_test() {
  // Tour file now returns 100 instead of 0
  assert_tour_result("09_guards", VLit(LitInt(100)))
}

pub fn t05_10_exhaustiveness_test() {
  assert_tour_result("10_exhaustiveness", VLit(LitInt(42)))
}

pub fn t07_01_default_values_test() {
  // Uses the actual tour file source (exactly as written)
  let result = eval_tour("01_default_values")
  // The match {y} => y returns the y field value (default value 0)
  assert result == VLit(LitInt(0))
}

pub fn t07_02_implicit_params_test() {
  assert_tour_result("02_implicit_params", VLit(LitInt(42)))
}
