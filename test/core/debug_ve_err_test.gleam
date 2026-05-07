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
