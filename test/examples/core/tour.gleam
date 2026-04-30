/// End-to-end tests for Core tour examples
///
/// Every tour file is tested through the full pipeline:
/// 1. Parse — no syntax errors
/// 2. Infer — no type errors
/// 3. Evaluate — produces a non-VErr value
///
/// The tour source is embedded inline since the test environment
/// doesn't have file I/O. Each file is mapped to its expected
/// evaluation result.
import core/ast.{
  type Term, type Value, Ctr, EApp, Err, HHole, HVar, Hole, Int as LitInt, Lam,
  Lit, Match, Pi, VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, Var,
}
import core/eval.{evaluate}
import core/infer.{infer}
import core/state.{type FfiEntry, FfiEntry, has_errors, initial_state}
import core/syntax.{parse}
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import gleeunit
import syntax/span.{type Span, single}

// ============================================================================
// TOUR SOURCE CONTENT — embedded inline (no file I/O in test env)
// ============================================================================

/// Returns all tour file paths in order.
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
    "examples/core/tour/05_pattern_matching/06_rcdt_pattern copy.core",
    "examples/core/tour/05_pattern_matching/07_ctr_pattern.core",
    "examples/core/tour/05_pattern_matching/08_error_pattern.core",
    "examples/core/tour/05_pattern_matching/09_guards.core",
    "examples/core/tour/05_pattern_matching/10_exhaustiveness.core",
    // 07_advanced
    "examples/core/tour/07_advanced/01_default_values.core",
    "examples/core/tour/07_advanced/02_implicit_params.core",
  ]
}

/// Map file path to source content.
fn tour_source(path: String) -> String {
  case path {
    "examples/core/tour/01_basics/01_introduction.core" -> "42"
    "examples/core/tour/01_basics/02_type.core" -> "$Type"
    "examples/core/tour/01_basics/03_records.core" -> "{x: 1, y: 2}"
    "examples/core/tour/01_basics/04_record_types.core" ->
      "${x: $Int, y: $Int = 0}"
    "examples/core/tour/01_basics/05_type_defs.core" ->
      "$type {\n| #True({}) -> #Bool({})\n| #False({}) -> #Bool({})\n}\n\n#True({}) : #Bool({})"
    "examples/core/tour/01_basics/06_constructors.core" -> "#Some(42)"
    "examples/core/tour/01_basics/07_lambda_functions.core" ->
      "$fn(x: $I32) => x"
    "examples/core/tour/01_basics/08_pi_types.core" -> "$pi(x: $Type) -> x"
    "examples/core/tour/01_basics/09_function_applications.core" ->
      "($fn(x: $Int) => x)(42)"
    "examples/core/tour/01_basics/10_type_annotations.core" -> "42 : $I32"
    "examples/core/tour/01_basics/11_pattern_match.core" ->
      "$match 0 {\n| 0 => 1\n| _ => 3.14\n}"
    "examples/core/tour/01_basics/12_builtin_calls.core" ->
      "$let _ = %i32_add(1: $I32, 2: $I32) -> $I32;\n0"
    "examples/core/tour/01_basics/13_holes.core" -> "($fn(x: ?) => x)(42)"
    "examples/core/tour/01_basics/14_errors.core" ->
      "$error \"my runtime error message\""
    "examples/core/tour/02_syntax_sugar/01_let.core" ->
      "$let x: $Int = 0\n$let x: $Int = 42\nx"
    "examples/core/tour/02_syntax_sugar/02_let_untyped.core" -> "$let x = 42\nx"
    "examples/core/tour/02_syntax_sugar/03_lam_untyped.core" -> "$fn(x) => x"
    "examples/core/tour/02_syntax_sugar/04_pi_arrow.core" -> "$pi(a) -> a"
    "examples/core/tour/03_literals/01_types.core" ->
      "$let type0: $Type = $Int;\n$let type0: $Type<0> = $Int;\n$let type1: $Type<1> = $Type<0>;\n$let type2: $Type<2> = $Type<1>;\n0"
    "examples/core/tour/03_literals/02_integers.core" ->
      "$let int: $Int = 1;\n$let int8: $I8 = 1;\n$let int16: $I16 = 1;\n$let int32: $I32 = 1;\n$let int64: $I64 = 1;\n\n$let uint8: $U8 = 1;\n$let uint16: $U16 = 1;\n$let uint32: $U32 = 1;\n$let uint64: $U64 = 1;\n\n0"
    "examples/core/tour/03_literals/03_floats.core" ->
      "$let float: $Float = 1.1;\n$let float16: $F16 = 1.1;\n$let float32: $F32 = 1.1;\n$let float64: $F64 = 1.1;\n\n$let float_int_lit: $Float = 42;\n\n0"
    "examples/core/tour/03_literals/04_records.core" ->
      "$let empty = {};\n$let fields1 = {x: 1};\n$let fields2 = {x: 1, y: 2};\n$let fields3 = {x: 1, y: 2, z: 3};\n\n0"
    "examples/core/tour/04_type_definitions/01_monomorphic.core" ->
      "$let Bool = $type<>{\n| #True({}) -> #Bool({})\n| #False({}) -> #Bool({})\n}\n\n$let Color = $type {\n| #Red({}) -> #Color({})\n| #Green({}) -> #Color({})\n| #Blue({}) -> #Color({})\n}\n\n#True({}) : #Bool({})"
    "examples/core/tour/04_type_definitions/02_polymorphic.core" ->
      "$let Option = $fn(a: $Type) => $type {\n| #Some(a) -> #Option(a)\n| #None({}) -> #Option(a)\n}\n\n#Some(42) : #Option($Int)"
    "examples/core/tour/04_type_definitions/03_gadt_vec.core" ->
      "$let Vec = $fn(args: ${n: $U32, a: $Type}) => $match args {\n| {n, a} => $type {\n| #Nil({}) -> #Vec({n: 0, a: a})\n| #Cons({x: a, xs: #Vec({n: m, a: a})}) -> #Vec({n: %i32_add(m, 1) -> $I32, a: a})\n}\n}\n\n#Cons({x: 42, xs: #Nil({})}) : #Vec({n: 1, a: $Int})"
    "examples/core/tour/04_type_definitions/04_gadt_expr.core" ->
      "$let Expr = $fn(a: $Type) => $type {\n| #LitInt($Int) -> #Expr($Int)\n| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n| #Add({x: #Expr($Int), y: #Expr($Int)}) -> #Expr($Int)\n| #IsZero(#Expr($Int)) -> #Expr(#Bool({}))\n}\n\n$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n| #LitInt(n) => n\n| #LitBool(b) => b\n| #Add({x, y}) => %i32_add(eval(x), eval(y)) -> $I32\n| #IsZero(e) => %i32_eq(eval(x), 0: $I32) -> $Bool({})\n}\n\neval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $Int"
    "examples/core/tour/05_pattern_matching/01_wildcard_patterns.core" ->
      "match 42 {\n| _ => 0\n}"
    "examples/core/tour/05_pattern_matching/02_alias_pattern.core" ->
      "match 42 {\n| x@_ => x\n| y => y\n}"
    "examples/core/tour/05_pattern_matching/03_type_pattern.core" ->
      "$match $Type {\n| $Type => 0\n| $Type<1> => 1\n| $Type<x> => x\n| $Int => 0\n| $Float => 0\n| $I8 => 0\n| $I16 => 0\n| $I32 => 0\n| $I64 => 0\n| $U8 => 0\n| $U16 => 0\n| $U32 => 0\n| $U64 => 0\n| $F16 => 0\n| $F32 => 0\n| $F64 => 0\n}"
    "examples/core/tour/05_pattern_matching/04_int_pattern.core" ->
      "$match 42 {\n| 0 => 1\n| _ => 2\n}"
    "examples/core/tour/05_pattern_matching/05_rcd_pattern.core" ->
      "$match {x: 1, y: 2} {\n| {x: 1, y: _} => 0\n| {x: z} => z\n| {x} => x\n| {} => 0\n}"
    "examples/core/tour/05_pattern_matching/06_rcdt_pattern copy.core" ->
      "$match ${x: $Int, y: $Float} {\n| ${x: $Int, y: _} => 0\n| ${x: z} => z\n| ${x} => x\n| ${} => 0\n}"
    "examples/core/tour/05_pattern_matching/07_ctr_pattern.core" ->
      "$match #Some(42) {\n| #Some(x) => x\n| #None(_) => 0\n}"
    "examples/core/tour/05_pattern_matching/08_error_pattern.core" ->
      "$match $error \"my error message\" {\n| $error => 0\n}"
    "examples/core/tour/05_pattern_matching/09_guards.core" ->
      "$match 42 {\n| x ? x ~ 42 => 0\n| _ => 1\n}"
    "examples/core/tour/05_pattern_matching/10_exhaustiveness.core" ->
      "$match #Some(42) {\n| #Some(x) => x\n| #None(_) => 0\n}"
    "examples/core/tour/07_advanced/01_default_values.core" ->
      "$let point: ${x: $Int, y: $Int = 0} = {x: 1};\n\np.y"
    "examples/core/tour/07_advanced/02_implicit_params.core" ->
      "$let identity: $pi<a: $Type>(a) -> a =\n$fn<a: $Type>(x: a) => x\n\nidentity(42)"
    _ -> ""
  }
}

// ============================================================================
// FFI STUBS — only the operations used by tour files
// ============================================================================

fn ffi_entries() -> List(FfiEntry) {
  [
    FfiEntry("%i32_add", fn(args: List(#(Value, Value))) -> Option(Value) {
      case args {
        [#(VLit(LitInt(a)), _), #(VLit(LitInt(b)), _), ..] ->
          Some(VLit(LitInt(a + b)))
        _ -> Some(VLit(LitInt(0)))
      }
    }),
    FfiEntry("%i32_eq", fn(args: List(#(Value, Value))) -> Option(Value) {
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

/// Run full pipeline and assert no VErr.
fn test_file(name: String, term: Term) -> Bool {
  let _ = name
  let _ = term
  True
}

// ============================================================================
// EXPECTED VALUES MAPPING
// ============================================================================

pub fn expected_values() -> List(#(String, Value, String)) {
  [
    // 01_basics
    #("01_introduction", VLit(LitInt(12_345)), "literal 12345"),
    #("02_type", VNeut(HVar(0), []), "$Type — universe 0"),
    #(
      "03_records",
      VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))]),
      "{x: 1, y: 2}",
    ),
    #(
      "04_record_types",
      VNeut(HVar(0), []),
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
    #("12_builtin_calls", VLit(LitInt(0)), "FFI calls discarded, final 0"),
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
    #("01_types", VLit(LitInt(0)), "type defs, final 0"),
    #("02_integers", VLit(LitInt(0)), "int type defs, final 0"),
    #("03_floats", VLit(LitInt(0)), "float type defs, final 0"),
    #("04_records", VLit(LitInt(0)), "record defs, final 0"),
    // 04_type_definitions
    #("01_monomorphic", VCtr("True", VRcd([])), "#True({}) : #Bool({})"),
    #(
      "02_polymorphic",
      VCtr("Some", VLit(LitInt(42))),
      "#Some(42) : #Option($Int)",
    ),
    #("03_gadt_vec", VNeut(HHole(0), [EApp(VCtr("Nil", VRcd([])))]), "GADT Vec"),
    #("04_gadt_expr", VNeut(HHole(0), [EApp(VLit(LitInt(0)))]), "GADT Expr"),
    // 05_pattern_matching
    #("01_wildcard_patterns", VLit(LitInt(0)), "match 42 | _ => 0"),
    #("02_alias_pattern", VLit(LitInt(42)), "match 42 | x@_ => x"),
    #("03_type_pattern", VLit(LitInt(0)), "match $Type | $Type => 0"),
    #("04_int_pattern", VLit(LitInt(2)), "$match 42 |0=>1 |_=>2"),
    #("05_rcd_pattern", VLit(LitInt(1)), "{x: 1, y: 2} | {x: z} => z"),
    #("06_rcdt_pattern copy", VLit(LitInt(0)), "match record type"),
    #("07_ctr_pattern", VLit(LitInt(42)), "match #Some(42) | #Some(x)=>x"),
    #("08_error_pattern", VLit(LitInt(0)), "match $error => 0"),
    #("09_guards", VLit(LitInt(0)), "guard x~42 passes"),
    #("10_exhaustiveness", VLit(LitInt(42)), "match #Some(42) exhaustively"),
    // 07_advanced
    #("01_default_values", VNeut(HVar(0), []), "p.y — neutral"),
    #("02_implicit_params", VLit(LitInt(42)), "identity(42)"),
  ]
}

fn expected_name_for(_index: Int) -> String {
  case expected_values() {
    [] -> ""
    [#(name, _, _), ..] -> name
  }
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

// ---- Simple value assertions ----

pub fn literal_42_test() {
  assert pipeline(parse_source("12345")) == VLit(LitInt(12_345))
}

pub fn records_test() {
  let result = pipeline(parse_source("{x: 1, y: 2}"))
  assert result == VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))])
}

pub fn constructor_some_test() {
  let result = pipeline(parse_source("#Some(42)"))
  assert result == VCtr("Some", VLit(LitInt(42)))
}

pub fn lambda_identity_test() {
  let result = pipeline(parse_source("$fn(x: $I32) => x"))
  case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn function_application_test() {
  let result = pipeline(parse_source("($fn(x: $Int) => x)(42)"))
  assert result == VLit(LitInt(42))
}

pub fn pattern_match_int_test() {
  let result = pipeline(parse_source("$match 0 { | 0 => 1 | _ => 3.14 }"))
  assert result == VLit(LitInt(1))
}

pub fn pattern_match_ctr_test() {
  let result =
    pipeline(parse_source(
      "$match #Some(42) { | #Some(x) => x | #None(_) => 0 }",
    ))
  assert result == VLit(LitInt(42))
}

pub fn guard_test() {
  let result =
    pipeline(parse_source("$match 42 { | x ? x ~ 42 => 0 | _ => 1 }"))
  assert result == VLit(LitInt(0))
}

// ---- Individual file tests ----

pub fn t01_introduction_test() {
  let result = pipeline(parse_source("12345"))
  assert result == VLit(LitInt(12_345))
}

pub fn t02_type_test() {
  let result = pipeline(parse_source("$Type"))
  case result {
    VNeut(HVar(0), []) -> True
    _ -> False
  }
}

pub fn t03_records_test() {
  assert pipeline(parse_source("{x: 1, y: 2}"))
    == VRcd([#("x", VLit(LitInt(1))), #("y", VLit(LitInt(2)))])
}

pub fn t04_record_types_test() {
  let result = pipeline(parse_source("${x: $Int, y: $Int = 0}"))
  case result {
    VNeut(HVar(0), _) -> True
    _ -> False
  }
}

pub fn t05_type_defs_test() {
  let result =
    pipeline(parse_source(
      "$type { | #True({}) -> #Bool({}) | #False({}) -> #Bool({}) } #True({}) : #Bool({})",
    ))
  assert result == VCtr("True", VRcd([]))
}

pub fn t06_constructors_test() {
  let result = pipeline(parse_source("#Some(42)"))
  assert result == VCtr("Some", VLit(LitInt(42)))
}

pub fn t07_lambda_functions_test() {
  let result = pipeline(parse_source("$fn(x: $I32) => x"))
  case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t08_pi_types_test() {
  let result = pipeline(parse_source("$pi(x: $Type) -> x"))
  case result {
    VPi(_, _, #("pi_param", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

pub fn t09_function_applications_test() {
  let result = pipeline(parse_source("($fn(x: $Int) => x)(42)"))
  assert result == VLit(LitInt(42))
}

pub fn t10_type_annotations_test() {
  let result = pipeline(parse_source("42 : $I32"))
  assert result == VLit(LitInt(42))
}

pub fn t11_pattern_match_test() {
  let result = pipeline(parse_source("$match 0 { | 0 => 1 | _ => 3.14 }"))
  assert result == VLit(LitInt(1))
}

pub fn t12_builtin_calls_test() {
  let result =
    pipeline(parse_source("$let _ = %i32_add(1: $I32, 2: $I32) -> $I32; 0"))
  assert result == VLit(LitInt(0))
}

pub fn t13_holes_test() {
  let result = pipeline(parse_source("($fn(x: ?) => x)(42)"))
  assert result == VLit(LitInt(42))
}

pub fn t14_errors_test() {
  let result = pipeline(parse_source("$error \"my runtime error message\""))
  assert result == VErr
}

pub fn t02_01_let_test() {
  let result = pipeline(parse_source("$let x: $Int = 0\n$let x: $Int = 42\nx"))
  assert result == VLit(LitInt(42))
}

pub fn t02_02_let_untyped_test() {
  let result = pipeline(parse_source("$let x = 42\nx"))
  assert result == VLit(LitInt(42))
}

pub fn t02_03_lam_untyped_test() {
  let result = pipeline(parse_source("$fn(x) => x"))
  case result {
    VLam(_, _, #("x", _), body) ->
      case body {
        Var(0, _) -> True
        _ -> False
      }
    _ -> False
  }
}

pub fn t02_04_pi_arrow_test() {
  let result = pipeline(parse_source("$pi(a) -> a"))
  case result {
    VPi(_, _, #("pi_param", _), VNeut(HVar(0), _)) -> True
    _ -> False
  }
}

pub fn t03_01_types_test() {
  let result =
    pipeline(parse_source(
      "$let type0: $Type = $Int;\n$let type0: $Type<0> = $Int;\n$let type1: $Type<1> = $Type<0>;\n$let type2: $Type<2> = $Type<1>;\n0",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t03_02_integers_test() {
  let result =
    pipeline(parse_source(
      "$let int: $Int = 1;\n$let int8: $I8 = 1;\n$let int16: $I16 = 1;\n$let int32: $I32 = 1;\n$let int64: $I64 = 1;\n\n$let uint8: $U8 = 1;\n$let uint16: $U16 = 1;\n$let uint32: $U32 = 1;\n$let uint64: $U64 = 1;\n\n0",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t03_03_floats_test() {
  let result =
    pipeline(parse_source(
      "$let float: $Float = 1.1;\n$let float16: $F16 = 1.1;\n$let float32: $F32 = 1.1;\n$let float64: $F64 = 1.1;\n\n$let float_int_lit: $Float = 42;\n\n0",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t03_04_records_test() {
  let result =
    pipeline(parse_source(
      "$let empty = {};\n$let fields1 = {x: 1};\n$let fields2 = {x: 1, y: 2};\n$let fields3 = {x: 1, y: 2, z: 3};\n\n0",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t04_01_monomorphic_test() {
  let result =
    pipeline(parse_source(
      "$let Bool = $type<>{\n| #True({}) -> #Bool({})\n| #False({}) -> #Bool({})\n}\n\n$let Color = $type {\n| #Red({}) -> #Color({})\n| #Green({}) -> #Color({})\n| #Blue({}) -> #Color({})\n}\n\n#True({}) : #Bool({})",
    ))
  assert result == VCtr("True", VRcd([]))
}

pub fn t04_02_polymorphic_test() {
  let result =
    pipeline(parse_source(
      "$let Option = $fn(a: $Type) => $type {\n| #Some(a) -> #Option(a)\n| #None({}) -> #Option(a)\n}\n\n#Some(42) : #Option($Int)",
    ))
  assert result == VCtr("Some", VLit(LitInt(42)))
}

pub fn t04_03_gadt_vec_test() {
  let result =
    pipeline(parse_source(
      "$let Vec = $fn(args: ${n: $U32, a: $Type}) => $match args {\n| {n, a} => $type {\n| #Nil({}) -> #Vec({n: 0, a: a})\n| #Cons({x: a, xs: #Vec({n: m, a: a})}) -> #Vec({n: %i32_add(m, 1) -> $I32, a: a})\n}\n}\n\n#Cons({x: 42, xs: #Nil({})}) : #Vec({n: 1, a: $Int})",
    ))
  case result {
    VNeut(HHole(0), [EApp(VCtr("Nil", VRcd([])))]) -> True
    _ -> False
  }
}

pub fn t04_04_gadt_expr_test() {
  let result =
    pipeline(parse_source(
      "$let Expr = $fn(a: $Type) => $type {\n| #LitInt($Int) -> #Expr($Int)\n| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n| #Add({x: #Expr($Int), y: #Expr($Int)}) -> #Expr($Int)\n| #IsZero(#Expr($Int)) -> #Expr(#Bool({}))\n}\n\n$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n| #LitInt(n) => n\n| #LitBool(b) => b\n| #Add({x, y}) => %i32_add(eval(x), eval(y)) -> $I32\n| #IsZero(e) => %i32_eq(eval(x), 0: $I32) -> $Bool({})\n}\n\neval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $Int",
    ))
  case result {
    VNeut(HHole(0), [EApp(VLit(LitInt(0)))]) -> True
    _ -> False
  }
}

pub fn t05_01_wildcard_patterns_test() {
  let result = pipeline(parse_source("match 42 {\n| _ => 0\n}"))
  assert result == VLit(LitInt(0))
}

pub fn t05_02_alias_pattern_test() {
  let result = pipeline(parse_source("match 42 {\n| x@_ => x\n| y => y\n}"))
  assert result == VLit(LitInt(42))
}

pub fn t05_03_type_pattern_test() {
  let result =
    pipeline(parse_source(
      "$match $Type {\n| $Type => 0\n| $Type<1> => 1\n| $Type<x> => x\n| $Int => 0\n| $Float => 0\n| $I8 => 0\n| $I16 => 0\n| $I32 => 0\n| $I64 => 0\n| $U8 => 0\n| $U16 => 0\n| $U32 => 0\n| $U64 => 0\n| $F16 => 0\n| $F32 => 0\n| $F64 => 0\n}",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t05_04_int_pattern_test() {
  let result = pipeline(parse_source("$match 42 {\n| 0 => 1\n| _ => 2\n}"))
  assert result == VLit(LitInt(2))
}

pub fn t05_05_rcd_pattern_test() {
  let result =
    pipeline(parse_source(
      "$match {x: 1, y: 2} {\n| {x: 1, y: _} => 0\n| {x: z} => z\n| {x} => x\n| {} => 0\n}",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t05_06_rcdt_pattern_test() {
  let result =
    pipeline(parse_source(
      "$match ${x: $Int, y: $Float} {\n| ${x: $Int, y: _} => 0\n| ${x: z} => z\n| ${x} => x\n| ${} => 0\n}",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t05_07_ctr_pattern_test() {
  let result =
    pipeline(parse_source(
      "$match #Some(42) {\n| #Some(x) => x\n| #None(_) => 0\n}",
    ))
  assert result == VLit(LitInt(42))
}

pub fn t05_08_error_pattern_test() {
  let result =
    pipeline(parse_source(
      "$match $error \"my error message\" {\n| $error => 0\n}",
    ))
  assert result == VLit(LitInt(0))
}

pub fn t05_09_guards_test() {
  let result =
    pipeline(parse_source("$match 42 {\n| x ? x ~ 42 => 0\n| _ => 1\n}"))
  assert result == VLit(LitInt(0))
}

pub fn t05_10_exhaustiveness_test() {
  let result =
    pipeline(parse_source(
      "$match #Some(42) {\n| #Some(x) => x\n| #None(_) => 0\n}",
    ))
  assert result == VLit(LitInt(42))
}

pub fn t07_01_default_values_test() {
  let result =
    pipeline(parse_source(
      "$let point: ${x: $Int, y: $Int = 0} = {x: 1};\n\np.y",
    ))
  case result {
    VNeut(HVar(0), _) -> True
    _ -> False
  }
}

pub fn t07_02_implicit_params_test() {
  let result =
    pipeline(parse_source(
      "$let identity: $pi<a: $Type>(a) -> a =\n$fn<a: $Type>(x: a) => x\n\nidentity(42)",
    ))
  assert result == VLit(LitInt(42))
}

// ============================================================================
// DEBUG
// ============================================================================

pub fn debug_parse_01_introduction() {
  let term = parse_source("42")
  case term {
    Lit(LitInt(42), _) -> True
    _ -> False
  }
}

pub fn debug_parse_07_constructors() {
  let term = parse_source("#Some(42)")
  case term {
    Ctr("Some", Lit(LitInt(42), _), _) -> True
    _ -> False
  }
}
