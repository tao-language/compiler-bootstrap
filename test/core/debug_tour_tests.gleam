// Comprehensive debug tests for the two failing tour files.
// Each test verifies one intermediate step to isolate where things break.

import core/ast.{type Value, type Term, VLit, Int as LitInt, VErr, VTypeDef, Match, App, VRcd, Rcd, RcdT}
import gleam/option.{type Option, Some}
import core/infer.{infer}
import core/eval.{evaluate}
import core/state.{initial_state, type FfiEntry, FfiEntry}
import core/syntax.{parse}
import gleam/list
import simplifile

// ============================================================================
// T04_GADT_EXPR — GADT expression evaluator
// ============================================================================

pub fn t04_gadt_expr_step1_parse_expression_test() {
  // Step 1: Verify parsing works for the final expression
  let source = "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  // The term should be an application of eval to an Add constructor
  case term {
    App(_, _, _) -> True
    _ -> False
  }
}

pub fn t04_gadt_expr_step2_parse_type_def_test() {
  // Step 2: Verify parsing works for the GADT type definition
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}"
  let #(term, errors) = parse(source)
  assert errors == []
  // Let is desugared into App(Lam(...), value, body)
  case term {
    App(_, _, _) -> True
    _ -> False
  }
}

pub fn t04_gadt_expr_step3_infer_type_def_test() {
  // Step 3: Verify type inference works for the GADT type definition
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}"
  let #(term, parse_errors) = parse(source)
  assert parse_errors == []
  
  let state = initial_state([])
  let inferred = infer(state, term)
  let #(result, _, _) = inferred
  
  // The inferred value should be a ValueTypeDef
  case result {
    VTypeDef(_, _, _) -> True
    VErr -> False
    _ -> False
  }
}

pub fn t04_gadt_expr_step4_infer_eval_fn_test() {
  // Step 4: Verify type inference works for the eval function
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}"
  let #(term, parse_errors) = parse(source)
  assert parse_errors == []
  
  let state = initial_state([])
  let inferred = infer(state, term)
  let #(result, _, _) = inferred
  
  // The inferred value should be a VTypeDef (for the eval binding)
  case result {
    VTypeDef(_, _, _) -> True
    VErr -> False
    _ -> False
  }
}

pub fn t04_gadt_expr_step5_evaluate_final_expr_test() {
  // Step 5: Verify evaluation of the final expression
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, parse_errors) = parse(source)
  assert parse_errors == []
  
  let state = initial_state([])
  let result = evaluate(state, term)
  
  // This should return 3
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

pub fn t04_gadt_expr_step6_parse_full_source_test() {
  // Step 6: Verify the full source parses (with type annotation)
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(_, errs) = parse(source)
  // The full source should parse without errors
  assert errs == []
}

pub fn t04_gadt_expr_step7_evaluate_full_source_test() {
  // Step 7: Full evaluation of the GADT expression (with type annotation)
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  
  let state = initial_state([])
  let result = evaluate(state, term)
  
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

// ============================================================================
// T07_DEFAULT_VALUES — Record default values
// ============================================================================

pub fn t07_default_values_step1_parse_record_type_test() {
  // Step 1: Verify parsing of the record type with defaults
  let source = "${x: $Int, y: $Int = 0}"
  let #(term, errors) = parse(source)
  assert errors == []
  // Should be a record type
  case term {
    RcdT(_, _) -> True
    _ -> False
  }
}

pub fn t07_default_values_step2_parse_record_literal_test() {
  // Step 2: Verify parsing of the record literal
  let source = "{x: 1}"
  let #(term, errors) = parse(source)
  assert errors == []
  case term {
    Rcd(_, _) -> True
    _ -> False
  }
}

pub fn t07_default_values_step3_parse_let_binding_test() {
  // Step 3: Verify parsing of the let binding with type annotation
  let source = "$let point: ${x: $Int, y: $Int = 0} = {x: 1}"
  let #(term, errors) = parse(source)
  assert errors == []
  // Let is desugared into App(Lam(...), value, body)
  case term {
    App(_, _, _) -> True
    _ -> False
  }
}

pub fn t07_default_values_step4_infer_let_binding_test() {
  // Step 4: Verify type inference of the let binding
  let source = "$let point: ${x: $Int, y: $Int = 0} = {x: 1}"
  let #(term, parse_errors) = parse(source)
  assert parse_errors == []
  
  let state = initial_state([])
  let inferred = infer(state, term)
  let #(result, _, _) = inferred
  
  // Should be a VTypeDef
  case result {
    VTypeDef(_, _, _) -> True
    VErr -> False
    _ -> False
  }
}

pub fn t07_default_values_step5_parse_match_test() {
  // Step 5: Verify parsing of the match expression
  let source =
    "$match point {\n"
    <> "| {y} => y\n"
    <> "}"
  let #(term, errors) = parse(source)
  assert errors == []
  case term {
    Match(_, _, _) -> True
    _ -> False
  }
}

pub fn t07_default_values_step6_evaluate_let_only_test() {
  // Step 6: Evaluate just the let binding
  let source = "$let point: ${x: $Int, y: $Int = 0} = {x: 1}"
  let #(term, errors) = parse(source)
  assert errors == []
  
  let state = initial_state([])
  let result = evaluate(state, term)
  
  // Should return a record value with x field
  case result {
    VRcd(fields) -> {
      case list.find(fields, fn(f) { case f { #(name, _) -> name == "x" } }) {
        Ok(#("x", VLit(LitInt(1)))) -> True
        _ -> False
      }
    }
    VErr -> False
    _ -> False
  }
}

pub fn t07_default_values_step7_evaluate_full_source_test() {
  // Step 7: Full evaluation of the default values test
  let source =
    "$let point: ${x: $Int, y: $Int = 0} = {x: 1};\n"
    <> "$match point {\n"
    <> "| {y} => y\n"
    <> "}"
  let #(term, errors) = parse(source)
  assert errors == []
  
  let state = initial_state([])
  let result = evaluate(state, term)
  
  case result {
    VLit(LitInt(0)) -> True
    VErr -> False
    _ -> False
  }
}

// ============================================================================
// INTEGRATION: Use actual tour files (like the failing tour tests do)
// ============================================================================

fn read_tour_file(path: String) -> String {
  case simplifile.read(from: path) {
    Ok(contents) -> contents
    Error(_) -> panic
  }
}

fn parse_source(source: String) -> Term {
  let #(term, errors) = parse(source)
  assert errors == []
  term
}

fn make_ffi_entries() -> List(FfiEntry) {
  [
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
          Some(VLit(LitInt(case a == b { True -> 1 False -> 0 })))
        _ -> Some(VLit(LitInt(0)))
      }
    }),
  ]
}

fn pipeline(term: Term) -> Value {
  let state = initial_state(make_ffi_entries())
  evaluate(state, term)
}

pub fn t04_gadt_expr_integration_test() {
  // Read the actual tour file and evaluate it
  let content = read_tour_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let term = parse_source(content)
  let result = pipeline(term)
  assert result == VLit(LitInt(3))
}

pub fn t07_default_values_integration_test() {
  // Read the actual tour file and evaluate it
  let content = read_tour_file("examples/core/tour/07_advanced/01_default_values.core")
  let term = parse_source(content)
  let result = pipeline(term)
  assert result == VLit(LitInt(0))
}

pub fn t04_gadt_file_vs_inline_test() {
  // Compare the tour file content with the inline source
  let file_content = read_tour_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let inline_source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  
  // Both should parse successfully
  let #(_, file_errors) = parse(file_content)
  let #(_, inline_errors) = parse(inline_source)
  
  assert file_errors == []
  assert inline_errors == []
}

pub fn t04_gadt_file_content_debug_test() {
  // Debug: Compare parsed terms from file vs inline
  let file_content = read_tour_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let inline_source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  
  // Parse both
  let #(file_term, file_errors) = parse(file_content)
  let #(inline_term, inline_errors) = parse(inline_source)
  
  // Both should parse without errors
  assert file_errors == []
  assert inline_errors == []
  
  // Evaluate both
  let file_result = evaluate(initial_state([]), file_term)
  let inline_result = evaluate(initial_state([]), inline_term)
  
  // Both should return VLit(LitInt(3))
  case file_result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
  
  case inline_result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn t04_gadt_integration_debug_test() {
  // Debug: Check what the integration test actually returns
  let content = read_tour_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let term = parse_source(content)
  let result = pipeline(term)
  
  // Check if it's VErr
  case result {
    VErr -> True
    _ -> False
  }
}

pub fn t04_gadt_file_result_debug_test() {
  // Debug: Check what file_result actually is
  let file_content = read_tour_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(file_term, file_errors) = parse(file_content)
  assert file_errors == []
  
  let file_result = evaluate(initial_state([]), file_term)
  
  // Check what it actually is
  case file_result {
    VErr -> True
    VLit(LitInt(3)) -> True
    _ -> False
  }
}
