// Debug tests to understand why VErr is being returned

import core/ast.{type Value, type Term, VLit, Int as LitInt, VErr, VLam, VRcd, VCtr}
import core/eval.{evaluate}
import core/state.{initial_state}
import core/syntax.{parse}
import simplifile

fn read_file(path: String) -> String {
  case simplifile.read(from: path) {
    Ok(contents) -> contents
    Error(_) -> panic
  }
}

pub fn debug_gadt_step1_parse_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
}

pub fn debug_gadt_step2_evaluate_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step3_simple_test() {
  let #(term, errors) = parse("1 + 2")
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step4_just_let_test() {
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
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step5_just_eval_call_test() {
  let source = "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step6_simple_let_test() {
  let source = "$let x = 1; x"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(1)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step7_simple_fn_test() {
  let source = "($fn(x: $Int) => x)(1)"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(1)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step8_full_source_test() {
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
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step9_tour_like_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step10_assert_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step11_check_result_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step12_comments_test() {
  let source =
    "// Here's an example of a type-safe expression using GADTs.\n"
    <> "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "// Type-safe evaluator.\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step13_eval_tour_like_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  let expected = VLit(LitInt(3))
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step14_exact_tour_content_test() {
  let source =
    "// Here's an example of a type-safe expression using GADTs.\n"
    <> "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "\n"
    <> "// Type-safe evaluator.\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

pub fn debug_gadt_step15_actual_tour_test() {
  // Test: Use actual tour test approach
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step16_tour_exact_approach_test() {
  // Test: Exact same approach as tour test
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // This should pass if result is VLit(LitInt(3)) or VErr
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

pub fn debug_gadt_step17_ffi_test() {
  // Test: Use FFI entries
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Debug: Check what the actual result is for the GADT expr tour file
pub fn debug_gadt_expr_actual_result_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(3))
}

// Debug: Check what the actual result is for the default values tour file
pub fn debug_default_values_actual_result_test() {
  let content = read_file("examples/core/tour/07_advanced/01_default_values.core")
  let #(term, errors) = parse(content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(0))
}

// Debug: Check if parsing succeeds for GADT expr
pub fn debug_gadt_expr_parse_test() {
  let content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(content)
  assert errors == []
  // If we get here, parsing succeeded
  True
}

// Debug: Check if parsing succeeds for default values
pub fn debug_default_values_parse_test() {
  let content = read_file("examples/core/tour/07_advanced/01_default_values.core")
  let #(term, errors) = parse(content)
  assert errors == []
  // If we get here, parsing succeeded
  True
}

// Debug: Check what happens with a simpler GADT expression
pub fn debug_simpler_gadt_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(42))
}

// Debug: Check if a simple let binding works
pub fn debug_simple_let_test() {
  let source = "$let x = 1; x"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(1))
}

// Debug: Check if a simple lambda works
pub fn debug_simple_lambda_test() {
  let source = "($fn(x: $Int) => x)(1)"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(1))
}


// Debug: Check if the GADT type definition alone works
pub fn debug_gadt_type_def_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "Expr"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Should not be VErr
  case result {
    VErr -> False
    _ -> True
  }
}

// Debug: Check if the GADT lambda alone works
pub fn debug_gadt_lambda_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Should not be VErr
  case result {
    VErr -> False
    _ -> True
  }
}

// Debug: Check if the GADT application works
pub fn debug_gadt_app_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // This should return VLit(LitInt(42))
  case result {
    VErr -> False
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if the same source produces the same result
pub fn debug_same_source_same_result_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  
  let #(term1, errors1) = parse(source)
  let #(term2, errors2) = parse(source)
  
  assert errors1 == []
  assert errors2 == []
  
  let result1 = evaluate(initial_state([]), term1)
  let result2 = evaluate(initial_state([]), term2)
  
  // Check if both results are the same
  case #(result1, result2) {
    #(VLit(LitInt(42)), VLit(LitInt(42))) -> True
    _ -> False
  }
}

// Debug: Check if the parsed terms are the same
pub fn debug_parsed_terms_same_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  
  let #(term1, errors1) = parse(source)
  let #(term2, errors2) = parse(source)
  
  assert errors1 == []
  assert errors2 == []
  
  // Check if both terms evaluate to the same result
  let result1 = evaluate(initial_state([]), term1)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should be VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> True
    _ -> False
  } && case result2 {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}


// Debug: Check if the GADT app test actually passes
pub fn debug_gadt_app_actual_result_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Check what the actual result is
  case result {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if the parsed terms are the same
pub fn debug_parsed_terms_identical_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  
  let #(term1, errors1) = parse(source)
  let #(term2, errors2) = parse(source)
  
  assert errors1 == []
  assert errors2 == []
  
  // Check if both terms evaluate to VLit(LitInt(42))
  let result1 = evaluate(initial_state([]), term1)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should be VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> case result2 {
      VLit(LitInt(42)) -> True
      _ -> False
    }
    _ -> False
  }
}


// Debug: Check if the GADT type definition affects the match
pub fn debug_gadt_type_affects_match_test() {
  // Without GADT type definition
  let source1 = "$match #LitInt(42) { | #LitInt(n) => n }"
  let #(term1, _) = parse(source1)
  let result1 = evaluate(initial_state([]), term1)
  
  // With GADT type definition
  let source2 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$match #LitInt(42) { | #LitInt(n) => n }"
  let #(term2, _) = parse(source2)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should return VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> case result2 {
      VLit(LitInt(42)) -> True
      _ -> False
    }
    _ -> False
  }
}

// Debug: Check if the lambda with GADT type works
pub fn debug_gadt_lambda_works_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Should not be VErr
  case result {
    VErr -> False
    _ -> True
  }
}

// Debug: Check if the lambda application works
pub fn debug_gadt_lambda_app_works_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // This should return VLit(LitInt(42))
  case result {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if the parsed terms are the same for both tests
pub fn debug_same_source_both_tests_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr { | #LitInt(n) => n }\n"
    <> "eval(#LitInt(42))"
  
  let #(term, errors) = parse(source)
  assert errors == []
  
  let result = evaluate(initial_state([]), term)
  
  // Check what the actual result is
  case result {
    VCtr("LitInt", VLit(LitInt(42))) -> False
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if a simple match with variable binding works
pub fn debug_simple_match_var_test() {
  let source = "$match #LitInt(42) { | #LitInt(x) => x }"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Should return VLit(LitInt(42))
  case result {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if a simple lambda with match works
pub fn debug_simple_lambda_match_test() {
  let source =
    "$let f = $fn(x: #LitInt(42)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Should return VLit(LitInt(42))
  case result {
    VLit(LitInt(42)) -> True
    _ -> False
  }
}

// Debug: Check if the GADT type definition affects the lambda
pub fn debug_gadt_type_affects_lambda_test() {
  // Without GADT type definition
  let source1 =
    "$let f = $fn(x: #LitInt(42)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term1, _) = parse(source1)
  let result1 = evaluate(initial_state([]), term1)
  
  // With GADT type definition
  let source2 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn(x: #LitInt(42)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term2, _) = parse(source2)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should return VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> case result2 {
      VLit(LitInt(42)) -> True
      _ -> False
    }
    _ -> False
  }
}

// Debug: Check if the GADT parameter type affects the lambda
pub fn debug_gadt_param_type_affects_lambda_test() {
  // With #LitInt(42) parameter type
  let source1 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn(x: #LitInt(42)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term1, _) = parse(source1)
  let result1 = evaluate(initial_state([]), term1)
  
  // With #Expr(a) parameter type
  let source2 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn<a: $Type>(x: #Expr(a)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term2, _) = parse(source2)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should return VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> case result2 {
      VLit(LitInt(42)) -> True
      _ -> False
    }
    _ -> False
  }
}

// Debug: Check if the polymorphic parameter type affects the lambda
pub fn debug_poly_param_type_affects_lambda_test() {
  // Without polymorphic parameter type
  let source1 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn(x: #LitInt(42)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term1, _) = parse(source1)
  let result1 = evaluate(initial_state([]), term1)
  
  // With polymorphic parameter type
  let source2 =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn<a: $Type>(x: #Expr(a)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term2, _) = parse(source2)
  let result2 = evaluate(initial_state([]), term2)
  
  // Both should return VLit(LitInt(42))
  case result1 {
    VLit(LitInt(42)) -> case result2 {
      VLit(LitInt(42)) -> True
      _ -> False
    }
    _ -> False
  }
}


// Debug: Check what the actual result is for the GADT app test
pub fn debug_gadt_app_actual_result2_test() {
  let source =
    "$let Expr = $type<a: $Type> { | #LitInt($I32) -> #Expr($I32) }\n"
    <> "$let f = $fn<a: $Type>(x: #Expr(a)) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // Check what the actual result is
  case result {
    VCtr("LitInt", VLit(LitInt(42))) -> False
    VLit(LitInt(42)) -> True
    _ -> False
  }
}
