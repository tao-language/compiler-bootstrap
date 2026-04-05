// ============================================================================
// MATCH MOTIVE HOLE ID TEST
// ============================================================================
/// Tests that multiple match expressions in the same module use unique hole IDs
/// for their motives. The desugar_match function creates a motive lambda with a
/// hole that gets unified with the result type. If all matches share the same
/// hole ID (like -999), unification can create infinite type errors.
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
import core/state.{initial_state, type State, State, InfiniteType, TypeMismatch}
import core/ast as cast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST: Two functions with match expressions should not share hole IDs
// ============================================================================
/// Two functions each containing a match expression. The motives should have
/// unique hole IDs to prevent unification conflicts.
pub fn two_match_expressions_no_conflict_test() {
  let source = "
type Bool = True | False

fn not(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}

fn negate(a: Bool) -> Bool {
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
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO InfiniteType errors
  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)
}

// ============================================================================
// TEST: Three functions with match expressions
// ============================================================================
/// Three functions each containing a match expression. Tests that three different
/// hole IDs are used, not all sharing -999.
pub fn three_match_expressions_no_conflict_test() {
  let source = "
type Bool = True | False

fn not(a: Bool) -> Bool {
  match a {
    | True -> False
    | False -> True
  }
}

fn nand(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> not(b)
    | False -> True
  }
}

fn nor(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> False
    | False -> not(b)
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
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO InfiniteType errors
  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)
}

// ============================================================================
// TEST: Match with different result types should not conflict
// ============================================================================
/// Two match expressions with DIFFERENT result types. If they share the same
/// hole ID, unification would try to equate the different types, causing
/// an infinite type error.
pub fn match_different_result_types_test() {
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

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO InfiniteType errors
  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)

  // Should have NO TypeMismatch errors (different result types should not unify)
  let has_type_mismatch = list.any(final_state.errors, fn(err) {
    case err {
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_type_mismatch |> should.equal(False)
}

// ============================================================================
// TEST: Nested match expressions
// ============================================================================
/// A function with nested match expressions. Each match should have its own
/// unique hole ID.
pub fn nested_match_expressions_test() {
  let source = "
type Bool = True | False
type Ordering = LT | GT

fn compare_bools(a: Bool, b: Bool) -> Ordering {
  match a {
    | True ->
      match b {
        | True -> LT
        | False -> GT
      }
    | False ->
      match b {
        | True -> GT
        | False -> LT
      }
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
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO InfiniteType errors
  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)

  // Should have NO TypeMismatch errors
  let has_type_mismatch2 = list.any(final_state.errors, fn(err) {
    case err {
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_type_mismatch2 |> should.equal(False)
}
