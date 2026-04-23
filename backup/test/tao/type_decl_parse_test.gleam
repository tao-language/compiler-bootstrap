// ============================================================================
// TYPE DECLARATION PARSER TESTS
// ============================================================================
/// Tests for parsing type declarations in Tao.
import gleam/int
import gleam/list
import gleeunit
import gleeunit/should
import tao/syntax.{parse_module, TypeDecl as TaoTypeDecl, SimpleFn as TaoSimpleFn, ConstructorDecl as TaoCtrDecl}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// SIMPLE TYPE DECL (two constructors, no params)
// ============================================================================

/// Parse `type Bool = True | False` and verify structure.
pub fn type_decl_two_constructors_test() {
  let source = "type Bool = True | False"
  let parse_result = parse_module(source, "test.tao")
  parse_result.errors |> should.equal([])
  list.length(parse_result.ast) |> should.equal(1)

  let first_expr = case parse_result.ast {
    [first, ..] -> first
    [] -> panic as "Expected at least one expression"
  }

  case first_expr {
    TaoTypeDecl(name, _type_params, constructors, _) -> {
      name |> should.equal("Bool")
      list.length(constructors) |> should.equal(2)

      // Extract constructor names
      let ctr_names = list.map(constructors, fn(ctr) {
        case ctr {
          TaoCtrDecl(ctr_name, _, _) -> ctr_name
        }
      })
      list.contains(ctr_names, "True") |> should.equal(True)
      list.contains(ctr_names, "False") |> should.equal(True)
    }
    _ -> panic as "Expected TypeDecl"
  }
}

// ============================================================================
// SINGLE CONSTRUCTOR
// ============================================================================

/// Parse `type Unit = Unit` — single constructor, no params.
pub fn type_decl_single_constructor_test() {
  let source = "type Unit = Unit"
  let parse_result = parse_module(source, "test.tao")
  parse_result.errors |> should.equal([])
  list.length(parse_result.ast) |> should.equal(1)

  let first_expr = case parse_result.ast {
    [first, ..] -> first
    [] -> panic as "Expected at least one expression"
  }

  case first_expr {
    TaoTypeDecl(name, _type_params, constructors, _) -> {
      name |> should.equal("Unit")
      list.length(constructors) |> should.equal(1)

      let ctr_names = list.map(constructors, fn(ctr) {
        case ctr {
          TaoCtrDecl(ctr_name, _, _) -> ctr_name
        }
      })
      list.contains(ctr_names, "Unit") |> should.equal(True)
    }
    _ -> panic as "Expected TypeDecl"
  }
}

// ============================================================================
// THREE CONSTRUCTORS
// ============================================================================

/// Parse `type Color = Red | Green | Blue` — three constructors.
pub fn type_decl_three_constructors_test() {
  let source = "type Color = Red | Green | Blue"
  let parse_result = parse_module(source, "test.tao")

  // Debug output
  let first_info = case parse_result.ast {
    [TaoTypeDecl(n, _tp, cs, _), ..] -> "TypeDecl(" <> n <> "," <> int.to_string(list.length(cs)) <> ")"
    [other, ..] -> "not_TypeDecl"
    [] -> "empty"
  }

  // Should have 3 constructors
  first_info |> should.equal("TypeDecl(Color,3)")

  let first_expr = case parse_result.ast {
    [first, ..] -> first
    [] -> panic as "Expected at least one expression"
  }

  case first_expr {
    TaoTypeDecl(name, _type_params, constructors, _) -> {
      name |> should.equal("Color")
      list.length(constructors) |> should.equal(3)

      let ctr_names = list.map(constructors, fn(ctr) {
        case ctr {
          TaoCtrDecl(ctr_name, _, _) -> ctr_name
        }
      })
      list.contains(ctr_names, "Red") |> should.equal(True)
      list.contains(ctr_names, "Green") |> should.equal(True)
      list.contains(ctr_names, "Blue") |> should.equal(True)
    }
    _ -> panic as "Expected TypeDecl"
  }
}

// ============================================================================
// TYPE DECL IN MODULE CONTEXT
// ============================================================================

/// Parse a module with type decl followed by functions.
pub fn type_decl_in_module_test() {
  let source = "
type Bool = True | False

fn not(b: Bool) -> Bool {
  match b {
    | True -> False
    | False -> True
  }
}
"
  let parse_result = parse_module(source, "test.tao")
  parse_result.errors |> should.equal([])
  list.length(parse_result.ast) |> should.equal(2)

  let expr_types = list.map(parse_result.ast, fn(expr) {
    case expr {
      TaoTypeDecl(n, _tp, cs, _) -> "TypeDecl(" <> n <> "," <> int.to_string(list.length(cs)) <> ")"
      TaoSimpleFn(n, _, _, _, _) -> "SimpleFn(" <> n <> ")"
      _ -> "other"
    }
  })

  case expr_types {
    ["TypeDecl(Bool,2)", "SimpleFn(not)"] -> Nil
    _ -> panic as "Unexpected expr types"
  }
}
