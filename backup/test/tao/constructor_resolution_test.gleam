// ============================================================================
// CONSTRUCTOR RESOLUTION TEST
// ============================================================================
/// Tests that constructor names (True, False, etc.) are correctly resolved
/// from Var expressions to CoreCtr terms during desugaring.
import gleam/list
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import tao/syntax.{parse_module}
import tao/test_api.{strip_test_lines, exprs_to_stmts}
import tao/ast.{Module, StmtFn, TVar}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import core/infer.{infer}
import core/state.{initial_state, type State, State, InfiniteType, TypeMismatch, CtrUndefined}
import core/ast as cast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST: Simple match with constructors
// ============================================================================
pub fn simple_match_constructors_test() {
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

  // Check that constructors are in the ctrs
  let ctr_names = list.map(dc.ctrs, fn(c) { c.0 })
  list.contains(ctr_names, "True") |> should.equal(True)
  list.contains(ctr_names, "False") |> should.equal(True)
  list.contains(ctr_names, "Bool") |> should.equal(True)

  // Type-check should produce NO errors
  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  list.length(final_state.errors) |> should.equal(0)
}

// ============================================================================
// TEST: Match with different result types
// ============================================================================
pub fn match_different_types_test() {
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

  // Check that constructors are in the ctrs
  let ctr_names = list.map(dc.ctrs, fn(c) { c.0 })
  list.contains(ctr_names, "True") |> should.equal(True)
  list.contains(ctr_names, "False") |> should.equal(True)
  list.contains(ctr_names, "LT") |> should.equal(True)
  list.contains(ctr_names, "GT") |> should.equal(True)

  // Type-check should produce NO errors
  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
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
