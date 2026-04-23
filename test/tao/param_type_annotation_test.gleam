// ============================================================================
// FUNCTION PARAMETER TYPE ANNOTATION TEST
// ============================================================================
/// Tests that function parameter type annotations are correctly parsed and
/// preserved through the desugaring pipeline.
import gleam/list
import gleam/option.{type Option, Some, None}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import tao/syntax.{parse_module}
import tao/test_api.{strip_test_lines, exprs_to_stmts}
import tao/ast.{Module, StmtFn, TVar}
import tao/desugar.{desugar_module}
import tao/global_context.{new_context, with_prelude}
import core/infer.{infer}
import core/state.{initial_state, type State, State, InfiniteType, TypeMismatch}
import core/ast as cast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST: Single param with type annotation
// ============================================================================
pub fn single_param_type_annotation_test() {
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

  // Check that the param has a type annotation
  let body = exprs_to_stmts(parse_result.ast)
  let has_param_type = list.any(body, fn(stmt) {
    case stmt {
      StmtFn(_, _, params, _, _, _) -> {
        list.any(params, fn(p) {
          case p.type_annotation {
            Some(TVar(name, _)) -> name == "Bool"
            Some(_) -> False
            None -> False
          }
        })
      }
      _ -> False
    }
  })
  has_param_type |> should.equal(True)

  // Type-check should produce NO InfiniteType errors
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)
  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)
}

// ============================================================================
// TEST: Two params with type annotations
// ============================================================================
pub fn two_params_type_annotations_test() {
  let source = "
type Bool = True | False

fn and(a: Bool, b: Bool) -> Bool {
  match a {
    | True -> b
    | False -> False
  }
}
"
  let code = strip_test_lines(source)
  let parse_result = parse_module(code, "test.tao")
  parse_result.errors |> should.equal([])

  // Check that both params have type annotations
  let body = exprs_to_stmts(parse_result.ast)
  let param_type_count = list.fold(body, 0, fn(acc, stmt) {
    case stmt {
      StmtFn(_, _, params, _, _, _) -> {
        let count = list.fold(params, 0, fn(pacc, p) {
          case p.type_annotation {
            Some(TVar(_, _)) -> pacc + 1
            _ -> pacc
          }
        })
        acc + count
      }
      _ -> acc
    }
  })
  param_type_count |> should.equal(2)

  // Type-check should produce NO InfiniteType errors
  let module = Module("test.tao", body, Span("test.tao", 0, 0, 0, 0))
  let ctx = new_context() |> with_prelude()
  let #(core_term, dc) = desugar_module(module, ctx)
  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)

  let has_type_mismatch = list.any(final_state.errors, fn(err) {
    case err {
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_type_mismatch |> should.equal(False)
}
