// ============================================================================
// PATTERN EXTRACTION UNIT TESTS
// ============================================================================
/// Unit tests for pattern extraction logic in tao/syntax.gleam
/// Tests the extract_pattern_from_clause_items function and related helpers.
import tao/syntax.{parse_module, extract_pattern_debug, pattern_ast_to_pattern, Var, Int as TaoInt}
import tao/ast.{MatchClause}
import syntax/grammar.{Span, ParseResult}
import gleam/list
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

const s0 = Span("test", 0, 0, 0, 0)

// ============================================================================
// PARSING TESTS
// ============================================================================

pub fn parse_wildcard_pattern_test() {
  // Test that wildcard pattern parses correctly
  let source = "match x { | _ -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok(_) -> True |> should.be_true
    Error(e) -> {
      // Log the error for debugging
      let _ = io.println("Parse error: " <> inspect_errors(e))
      False |> should.be_true
    }
  }
}

pub fn parse_variable_pattern_test() {
  // Test that variable pattern parses correctly
  let source = "match x { | n -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok(_) -> True |> should.be_true
    Error(_) -> False |> should.be_true
  }
}

pub fn parse_literal_pattern_test() {
  // Test that literal pattern parses correctly
  let source = "match x { | 0 -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok(_) -> True |> should.be_true
    Error(_) -> False |> should.be_true
  }
}

pub fn parse_constructor_pattern_test() {
  // Test that constructor pattern parses correctly
  let source = "match x { | Some(n) -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok(_) -> True |> should.be_true
    Error(_) -> False |> should.be_true
  }
}

// ============================================================================
// PATTERN CONVERSION TESTS
// ============================================================================

pub fn pattern_ast_to_pattern_wildcard_test() {
  // Test conversion of wildcard Var to PWild
  let expr = Var("_", s0)
  let pattern = pattern_ast_to_pattern(expr)
  
  // Pattern should be PWild
  case pattern {
    PWild(_) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn pattern_ast_to_pattern_variable_test() {
  // Test conversion of variable Var to PVar
  let expr = Var("n", s0)
  let pattern = pattern_ast_to_pattern(expr)
  
  // Pattern should be PVar
  case pattern {
    PVar("n", _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

pub fn pattern_ast_to_pattern_literal_test() {
  // Test conversion of Int literal to PLit
  let expr = TaoInt(42, s0)
  let pattern = pattern_ast_to_pattern(expr)
  
  // Pattern should be PLit
  case pattern {
    PLit(42, _) -> True |> should.be_true
    _ -> False |> should.be_true
  }
}

// ============================================================================
// CLAUSE STRUCTURE TESTS
// ============================================================================

pub fn clause_structure_wildcard_test() {
  // Test that wildcard clause has correct structure
  let source = "match x { | _ -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok([Match(scrutinee, clauses, _)]) -> {
      // Check scrutinee
      case scrutinee {
        Var("x", _) -> True |> should.be_true
        _ -> False |> should.be_true
      }
      
      // Check clause count
      list.length(clauses) |> should.equal(1)
      
      // Check clause structure
      case clauses {
        [MatchClause(pattern, guard, body, _)] -> {
          // Guard should be None
          case guard {
            None -> True |> should.be_true
            Some(_) -> False |> should.be_true
          }
          
          // Body should be Int(100)
          case body {
            TaoInt(100, _) -> True |> should.be_true
            _ -> False |> should.be_true
          }
          
          // Pattern should be PWild (after conversion)
          case pattern {
            PWild(_) -> True |> should.be_true
            _ -> False |> should.be_true
          }
        }
        _ -> False |> should.be_true
      }
    }
    _ -> False |> should.be_true
  }
}

pub fn clause_structure_variable_test() {
  // Test that variable clause has correct structure
  let source = "match x { | n -> 100 }"
  let result = parse_module(source)
  
  case result {
    Ok([Match(_, clauses, _)]) -> {
      case clauses {
        [MatchClause(pattern, _, _, _)] -> {
          // Pattern should be PVar
          case pattern {
            PVar("n", _) -> True |> should.be_true
            _ -> False |> should.be_true
          }
        }
        _ -> False |> should.be_true
      }
    }
    _ -> False |> should.be_true
  }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

fn inspect_errors(errors: List(ParseError)) -> String {
  errors
  |> list.map(fn(e) {
    case e {
      ParseError(span, msg) -> msg <> " at " <> span.file <> ":" <> int.to_string(span.start_line)
    }
  })
  |> string.join("; ")
}
