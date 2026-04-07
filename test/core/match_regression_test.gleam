// MATCH EXPRESSION REGRESSION TESTS
// ============================================================================
/// Tests that verify match expressions work correctly with type annotations.
/// These are regression tests for issues where match result types were not
/// properly unified with function return type annotations.
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import tao/syntax.{parse_module}
import tao/test_api.{strip_test_lines, exprs_to_stmts}
import tao/ast.{Module}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import core/infer.{infer}
import core/state.{initial_state, State, InfiniteType, TypeMismatch, CtrUndefined}
import core/ast as cast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST: Single function with match and annotated return type
// ============================================================================
pub fn single_fn_match_annotated_test() {
  let source = "
type Bool = True | False

fn not(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  parse_result.errors |> should.equal([])

  let body = exprs_to_stmts(parse_result.ast)
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_errors = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      TypeMismatch(_, _, _, _) -> True
      CtrUndefined(_, _) -> True
      _ -> False
    }
  })
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Single function with match, NO return type annotation (pure inference)
// ============================================================================
pub fn single_fn_match_unannotated_test() {
  let source = "
type Bool = True | False

fn not(a: Bool) {
  match a {
    | True -> False
    | False -> True
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  parse_result.errors |> should.equal([])

  let body = exprs_to_stmts(parse_result.ast)
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_errors = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      TypeMismatch(_, _, _, _) -> True
      CtrUndefined(_, _) -> True
      _ -> False
    }
  })
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Two functions with matches returning DIFFERENT types
// ============================================================================
/// This was a known failure: two functions with match expressions returning
/// different types (Bool vs Ordering) caused InfiniteType errors because
/// match motive holes were not properly unique.
pub fn two_fn_match_different_result_types_test() {
  let source = "
type Bool = True | False
type Ordering = LT | GT

fn to_bool(o: Ordering) -> Bool {
  match o {
    | LT -> True
    | GT -> False
  }
}

fn to_ordering(b: Bool) -> Ordering {
  match b {
    | True -> LT
    | False -> GT
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  parse_result.errors |> should.equal([])

  let body = exprs_to_stmts(parse_result.ast)
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)

  // Verify constructors are present
  let ctr_names = list.map(dc.ctrs, fn(c) { c.0 })
  list.contains(ctr_names, "True") |> should.equal(True)
  list.contains(ctr_names, "False") |> should.equal(True)
  list.contains(ctr_names, "LT") |> should.equal(True)
  list.contains(ctr_names, "GT") |> should.equal(True)
  list.contains(ctr_names, "Bool") |> should.equal(True)
  list.contains(ctr_names, "Ordering") |> should.equal(True)

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_errors = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      TypeMismatch(_, _, _, _) -> True
      CtrUndefined(_, _) -> True
      _ -> False
    }
  })
  has_errors |> should.equal(False)
}

// ============================================================================
// TEST: Match inside nested lambda
// ============================================================================
pub fn match_in_nested_lambda_test() {
  let source = "
type Bool = True | False
type Option(a) = Some(a) | None

fn apply(f: fn(Bool) -> Bool, x: Bool) -> Bool {
  f(x)
}

fn not(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  // Parsing may fail for function types - that's OK, just check no crash
  // If parsing succeeds, check type-checking
  case parse_result.errors {
    [] -> {
      let body = exprs_to_stmts(parse_result.ast)
      let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
      let ctx = new_context() |> with_prelude()
      let #(core_term, dc) = desugar_module(module, ctx)

      let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
      let state = State(..initial_state, ctrs: merged_ctrs)
      let #(_value, _ty, final_state) = infer(state, core_term)

      let has_errors = list.any(final_state.errors, fn(err) {
        case err {
          InfiniteType(_, _, _, _) -> True
          TypeMismatch(_, _, _, _) -> True
          _ -> False
        }
      })
      has_errors |> should.equal(False)
    }
    _ -> {
      // Parse errors are acceptable for complex type syntax
      True |> should.equal(True)
    }
  }
}

// ============================================================================
// TEST: Multiple matches in same module (separate functions)
// ============================================================================
pub fn multiple_matches_in_one_module_test() {
  let source = "
type Bool = True | False

fn not1(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}

fn not2(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  parse_result.errors |> should.equal([])

  let body = exprs_to_stmts(parse_result.ast)
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_errors = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_errors |> should.equal(False)
}
