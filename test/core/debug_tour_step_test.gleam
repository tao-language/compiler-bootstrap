// Debug tests to trace through each step of the tour file evaluation

import core/ast.{type Value, VLit, Int as LitInt, VErr}
import core/eval.{evaluate}
import core/state.{initial_state}
import core/syntax.{parse}
import simplifile
import gleam/string

fn read_file(path: String) -> String {
  case simplifile.read(from: path) {
    Ok(contents) -> contents
    Error(_) -> panic
  }
}

// Step 1: Parse the tour file and check that parsing succeeds
pub fn step1_parse_succeeds_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  // Check that parsing succeeds
  case errors {
    [] -> True
    _ -> False
  }
}

// Step 2: Parse a simple tour-like expression (without comments)
pub fn step2_simple_tour_like_test() {
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
    VErr -> True
    _ -> False
  }
}

// Step 3: Check without type annotation
pub fn step3_no_type_annotation_test() {
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
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 4: Check if the issue is with the GADT type definition
pub fn step4_no_gadt_type_test() {
  // Skip the GADT type definition, just use the eval function
  let source =
    "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 5: Check the exact tour file content byte by byte
pub fn step5_file_content_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  // Check that the content contains the expected strings
  let has_let_expr = string.contains(file_content, "$let Expr")
  let has_let_eval = string.contains(file_content, "$let eval")
  let has_eval_call = string.contains(file_content, "eval(#Add")
  let has_type_annotation = string.contains(file_content, ": $I32")
  has_let_expr && has_let_eval && has_eval_call && has_type_annotation
}

// Step 6: Check if the issue is with the comments
pub fn step6_with_comments_test() {
  let source =
    "// Comment 1\n"
    <> "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "// Comment 2\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "// Comment 3\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 7: Check the tour file content with assert
pub fn step7_tour_file_assert_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 8: Check the tour file content with strict assert
pub fn step8_tour_file_strict_assert_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(3))
}

// Step 9: Check the tour file content with initial_state(ffi_entries)
pub fn step9_ffi_entries_test() {
  // This test uses the same approach as the tour test
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 10: Check a minimal GADT expression
pub fn step10_minimal_gadt_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "}\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(42)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 11: Check with extra newline between type def and eval
pub fn step11_extra_newline_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "\n"  // Extra newline
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
    VErr -> True
    _ -> False
  }
}

// Step 12: Check with trailing newline
pub fn step12_trailing_newline_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "\n"  // Trailing newline
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 13: Check with comments and extra newlines
pub fn step13_comments_and_newlines_test() {
  let source =
    "// Comment 1\n"
    <> "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "\n"
    <> "// Comment 2\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "\n"
    <> "// Comment 3\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 14: Check the exact tour file content (including trailing newline)
pub fn step14_exact_tour_content_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 15: Check if the issue is with the $match expression in the eval function
pub fn step15_match_in_fn_test() {
  let source =
    "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 16: Check if the issue is with the recursive call in the match
pub fn step16_recursive_match_test() {
  let source =
    "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 17: Compare parsed terms from file vs inline source
pub fn step17_compare_parsed_terms_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let inline_source =
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
    <> "\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  
  // Check that file content matches inline source
  let contents_match = file_content == inline_source
  
  // Parse both and check that parsing succeeds for both
  let #(file_term, file_errors) = parse(file_content)
  let #(inline_term, inline_errors) = parse(inline_source)
  
  let file_parse_ok = file_errors == []
  let inline_parse_ok = inline_errors == []
  
  // Evaluate both and check results
  let file_result = evaluate(initial_state([]), file_term)
  let inline_result = evaluate(initial_state([]), inline_term)
  
  // Check if results are the same
  let results_same = case #(file_result, inline_result) {
    #(VLit(LitInt(3)), VLit(LitInt(3))) -> True
    #(VErr, VErr) -> True
    _ -> False
  }
  
  contents_match && file_parse_ok && inline_parse_ok && results_same
}

// Step 18: Check the inline source with assert
pub fn step18_inline_source_assert_test() {
  let inline_source =
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
    <> "\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(inline_source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  assert result == VLit(LitInt(3))
}

// Step 19: Check if VErr is the actual result for the minimal GADT
pub fn step19_minimal_gadt_strict_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "}\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // This should pass if result is VLit(Int(42)) or VErr
  case result {
    VLit(LitInt(42)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 20: Check if VErr is the actual result for the full GADT
pub fn step20_full_gadt_strict_test() {
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
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  // This should pass if result is VLit(Int(3)) or VErr
  case result {
    VLit(LitInt(3)) -> True
    VErr -> True
    _ -> False
  }
}

// Step 21: Check if the result is VErr for the minimal GADT
pub fn step21_minimal_gadt_ve_err_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "}\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

// Step 22: Check if the result is VErr for the full GADT
pub fn step22_full_gadt_ve_err_test() {
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
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

// Step 23: Check if a simple let binding works
pub fn step23_simple_let_test() {
  let source = "$let x = 1; x"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(1)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 24: Check if a simple function works
pub fn step24_simple_fn_test() {
  let source = "($fn(x: $Int) => x)(1)"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(1)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 25: Check if a let binding with a function works
pub fn step25_let_fn_test() {
  let source = "$let f = $fn(x: $Int) => x; f(1)"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(1)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 26: Check if a let binding with a match works
pub fn step26_let_match_test() {
  let source =
    "$let f = $fn(x: $Int) => $match x { | #LitInt(n) => n }\n"
    <> "f(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(42)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 27: Check if a let binding with a recursive function works
pub fn step27_let_recursive_fn_test() {
  let source =
    "$let add = $fn(a: $Int, b: $Int) => %i32_add(a, b)\n"
    <> "add(1, 2)"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 28: Check if a let binding with a GADT type definition works
pub fn step28_gadt_type_def_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "}\n"
    <> "Expr"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> False
    _ -> True
  }
}

// Step 29: Check if a let binding with a GADT type definition and eval works
pub fn step29_gadt_eval_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "}\n"
    <> "eval(#LitInt(42))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(42)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 30: Check if the Add constructor works
pub fn step30_add_constructor_test() {
  let source =
    "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "}\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "}\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)}))"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 31: Check if the full GADT expression works (without type annotation)
pub fn step31_full_gadt_no_annotation_test() {
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
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 32: Check if the full GADT expression works (with type annotation)
pub fn step32_full_gadt_with_annotation_test() {
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
    VErr -> False
    _ -> False
  }
}

// Step 33: Check if the tour file content without comments works
pub fn step33_tour_file_no_comments_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  // Remove comments
  let no_comments = string.replace(file_content, "// Here's an example of a type-safe expression using GADTs.\n", "")
  let no_comments = string.replace(no_comments, "// Type-safe evaluator.\n", "")
  let #(term, errors) = parse(no_comments)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    VErr -> False
    _ -> False
  }
}

// Step 34: Check if the inline source with comments evaluates to VErr
pub fn step34_inline_source_comments_ve_err_test() {
  let source =
    "// Comment 1\n"
    <> "$let Expr = $type<a: $Type> {\n"
    <> "| #LitInt($I32) -> #Expr($I32)\n"
    <> "| #LitBool(#Bool({})) -> #Expr(#Bool({}))\n"
    <> "| #Add({x: #Expr($I32), y: #Expr($I32)}) -> #Expr($I32)\n"
    <> "| #IsZero(#Expr($I32)) -> #Expr(#Bool({}))\n"
    <> "}\n"
    <> "// Comment 2\n"
    <> "$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {\n"
    <> "| #LitInt(n) => n\n"
    <> "| #LitBool(b) => b\n"
    <> "| #Add({x, y}) => %i32_add(eval(x), eval(y))\n"
    <> "| #IsZero(e) => %i32_eq(eval(x), 0: $I32)\n"
    <> "}\n"
    <> "// Comment 3\n"
    <> "eval(#Add({x: #LitInt(1), y: #LitInt(2)})) : $I32"
  let #(term, errors) = parse(source)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

// Step 35: Check if the tour file with comments evaluates to VErr
pub fn step35_tour_file_comments_ve_err_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let #(term, errors) = parse(file_content)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VErr -> True
    _ -> False
  }
}

// Step 36: Check if the tour file without comments evaluates to VLit(Int(3))
pub fn step36_tour_file_no_comments_ve_lit_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  // Remove comments
  let no_comments = string.replace(file_content, "// Here's an example of a type-safe expression using GADTs.\n", "")
  let no_comments = string.replace(no_comments, "// Type-safe evaluator.\n", "")
  let #(term, errors) = parse(no_comments)
  assert errors == []
  let result = evaluate(initial_state([]), term)
  case result {
    VLit(LitInt(3)) -> True
    _ -> False
  }
}

// Step 37: Check if the parsed terms are the same
pub fn step37_parse_compare_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let no_comments = string.replace(file_content, "// Here's an example of a type-safe expression using GADTs.\n", "")
  let no_comments = string.replace(no_comments, "// Type-safe evaluator.\n", "")
  
  let #(file_term, file_errors) = parse(file_content)
  let #(no_comments_term, no_comments_errors) = parse(no_comments)
  
  // Check that both parse successfully
  let file_parse_ok = file_errors == []
  let no_comments_parse_ok = no_comments_errors == []
  
  // Check if both terms evaluate to the same result
  let file_result = evaluate(initial_state([]), file_term)
  let no_comments_result = evaluate(initial_state([]), no_comments_term)
  
  // Check if results are the same
  let results_same = case #(file_result, no_comments_result) {
    #(VLit(LitInt(3)), VLit(LitInt(3))) -> True
    #(VErr, VErr) -> True
    _ -> False
  }
  
  file_parse_ok && no_comments_parse_ok && results_same
}

// Step 38: Check what the actual results are
pub fn step38_check_actual_results_test() {
  let file_content = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let no_comments = string.replace(file_content, "// Here's an example of a type-safe expression using GADTs.\n", "")
  let no_comments = string.replace(no_comments, "// Type-safe evaluator.\n", "")
  
  let #(file_term, file_errors) = parse(file_content)
  let #(no_comments_term, no_comments_errors) = parse(no_comments)
  
  assert file_errors == []
  assert no_comments_errors == []
  
  let file_result = evaluate(initial_state([]), file_term)
  let no_comments_result = evaluate(initial_state([]), no_comments_term)
  
  // Check if file_result is VErr
  let file_is_ve_err = case file_result { VErr -> True _ -> False }
  
  // Check if no_comments_result is VLit(Int(3))
  let no_comments_is_vlit = case no_comments_result { VLit(LitInt(3)) -> True _ -> False }
  
  // If file_result is VErr and no_comments_result is VLit(Int(3)), then the results are different
  file_is_ve_err && no_comments_is_vlit
}

// Step 39: Check if the issue is with the read_file function
pub fn step39_read_file_test() {
  let content1 = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  let content2 = read_file("examples/core/tour/04_type_definitions/04_gadt_expr.core")
  // Check that reading the file twice returns the same content
  content1 == content2
}
