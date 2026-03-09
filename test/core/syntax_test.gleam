// ============================================================================
// CORE LANGUAGE SYNTAX TESTS
// ============================================================================
/// Round-trip tests for the core language syntax (parser and formatter).
///
/// Each test follows this pattern:
/// 1. Parse source to AST
/// 2. Verify AST structure
/// 3. Format AST back to source
/// 4. Verify formatted source matches expected
///
/// Syntax reference:
/// - Variables: `x`
/// - Literals: `42`
/// - Lambda: `x -> body`
/// - Pi types: `(x : A) -> B`
/// - Application: `f(x)`
/// - Type annotations: `x : $I32`
/// - Field access: `record.field`
/// - Records: `{}`
/// - Constructors: `#True`, `#Some`, `#Maybe(a)`
/// - Type universes: `$Type`, `$Type(1)`
/// - Holes: `?`, `?1`, `?2`
/// - Literal types: `$I32`, `$I64`, `$F64`
import core/core.{
  Ann, App, Ctr, Dot, F64T, Hole, I32, I32T, I64T, Lam, Lit, LitT, Pi, Rcd, Term, Typ, Var,
}
import syntax/grammar.{Span, type Span}
import core/syntax
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn test_span() -> Span {
  Span("test", 1, 1, 1, 1)
}

// ============================================================================
// VARIABLE TESTS
// ============================================================================

pub fn roundtrip_var_test() {
  // Free variables format as var0 (De Bruijn index with no binding in scope)
  let source = "x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Var(0), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_var_underscore_test() {
  // Underscore also formats as var0 (free variable)
  let source = "_"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Var(0), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

// ============================================================================
// LITERAL TESTS
// ============================================================================

pub fn roundtrip_lit_zero_test() {
  let source = "0"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Lit(I32(0)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_lit_positive_test() {
  let source = "42"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Lit(I32(42)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// LAMBDA TESTS
// ============================================================================

pub fn roundtrip_lambda_simple_test() {
  let source = "x -> x"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  // Verify round-trip: parse then format should give same source
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_lambda_different_var_test() {
  let source = "y -> y"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_lambda_nested_test() {
  let source = "x -> y -> y"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// PI TYPE TESTS
// ============================================================================

pub fn roundtrip_pi_simple_test() {
  let source = "(x : $I32) -> $I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_pi_with_type_universe_test() {
  let source = "(x : $Type) -> $Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_pi_with_level_test() {
  let source = "(x : $Type(1)) -> $Type(1)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// APPLICATION TESTS
// ============================================================================

pub fn roundtrip_app_simple_test() {
  let source = "f(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(App(Term(Var(0), _), Term(Var(0), _)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0)")
}

pub fn roundtrip_app_with_literal_test() {
  let source = "f(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(App(Term(Var(0), _), Term(Lit(I32(42)), _)), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(42)")
}

pub fn roundtrip_app_nested_test() {
  let source = "f(g(x))"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(App(Term(Var(0), _), Term(App(Term(Var(0), _), Term(Var(0), _)), _)), _) ->
      True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0(var0(var0))")
}

// ============================================================================
// TYPE ANNOTATION TESTS
// ============================================================================

pub fn roundtrip_annotation_simple_test() {
  let source = "x : $I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0 : $I32")
}

pub fn roundtrip_annotation_with_type_universe_test() {
  let source = "x : $Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0 : $Type")
}

// ============================================================================
// FIELD ACCESS TESTS
// ============================================================================

pub fn roundtrip_field_access_simple_test() {
  let source = "x.field"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Dot(Term(Var(0), _), "field"), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0.field")
}

// ============================================================================
// CONSTRUCTOR TESTS
// ============================================================================

pub fn roundtrip_constructor_nullary_test() {
  let source = "#True"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_some_test() {
  let source = "#Some"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_none_test() {
  let source = "#None"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_constructor_with_arg_test() {
  let source = "#Some(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("#Some(var0)")
}

// ============================================================================
// TYPE UNIVERSE TESTS
// ============================================================================

pub fn roundtrip_type_universe_zero_test() {
  let source = "$Type"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_type_universe_one_test() {
  let source = "$Type(1)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_type_universe_two_test() {
  let source = "$Type(2)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// LITERAL TYPE TESTS
// ============================================================================

pub fn roundtrip_litt_i32_test() {
  let source = "$I32"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_i64_test() {
  let source = "$I64"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_litt_f64_test() {
  let source = "$F64"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// HOLE TESTS
// ============================================================================

pub fn roundtrip_hole_simple_test() {
  let source = "?"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Hole(0), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_hole_with_id_test() {
  let source = "?1"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Hole(1), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_hole_with_id_two_test() {
  let source = "?2"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Hole(2), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// RECORD TESTS
// ============================================================================

pub fn roundtrip_record_empty_test() {
  let source = "{}"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Rcd([]), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// PARENTHESIS TESTS
// ============================================================================

pub fn roundtrip_parens_simple_test() {
  let source = "(x)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  case result.ast {
    Term(Var(0), _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("var0")
}

pub fn roundtrip_parens_preserved_when_needed_test() {
  let source = "(x -> x)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

// ============================================================================
// COMPLEX EXPRESSION TESTS
// ============================================================================

pub fn roundtrip_lambda_in_app_test() {
  let source = "(x -> x)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_pi_in_app_test() {
  let source = "((x : $I32) -> $I32)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal(source)
}

pub fn roundtrip_annotation_in_app_test() {
  let source = "(x : $I32)(42)"
  let result = syntax.parse(source)
  result.errors |> should.equal([])
  let formatted = syntax.format(result.ast)
  formatted |> should.equal("(var0 : $I32)(42)")
}
