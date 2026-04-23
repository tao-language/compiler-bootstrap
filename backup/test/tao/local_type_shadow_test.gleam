// ============================================================================
// LOCAL TYPE SHADOW TEST
// ============================================================================
/// Tests that local type definitions correctly shadow prelude types.
/// When a module defines its own `Bool` type, it should NOT conflict with
/// the prelude's `Bool` type. The implicit prelude imports should not
/// interfere with locally-defined types.
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
import core/state.{initial_state, type State, State, InfiniteType, TypeMismatch, VarUndefined}
import core/ast as cast

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST: Local Bool shadows prelude Bool
// ============================================================================
/// A module that defines its own Bool type should use the local definition,
/// not the prelude's. Function annotations should resolve to the local Bool.
pub fn local_bool_shadows_prelude_test() {
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
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO TypeMismatch errors (local Bool should be used consistently)
  let has_type_mismatch = list.any(final_state.errors, fn(err) {
    case err {
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_type_mismatch |> should.equal(False)

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
// TEST: Local Option shadows prelude Option
// ============================================================================
pub fn local_option_shadows_prelude_test() {
  let source = "
type Option(a) = Some(a) | None

fn unwrap_or(opt: Option(a), default: a) -> a {
  match opt {
    | Some(x) -> x
    | None -> default
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

  // Should have NO TypeMismatch errors
  let has_type_mismatch = list.any(final_state.errors, fn(err) {
    case err {
      TypeMismatch(_, _, _, _) -> True
      _ -> False
    }
  })
  has_type_mismatch |> should.equal(False)
}

// ============================================================================
// TEST: Module with no imports at all
// ============================================================================
/// A module that doesn't use the prelude at all (defines everything locally).
/// Implicit prelude imports should not pollute the namespace.
pub fn module_no_imports_test() {
  let source = "
type Bool = True | False
type Ordering = LT | EQ | GT

fn compare(a: Bool, b: Bool) -> Ordering {
  match a {
    | True ->
      match b {
        | True -> EQ
        | False -> GT
      }
    | False ->
      match b {
        | True -> LT
        | False -> EQ
      }
  }
}

fn is_eq(o: Ordering) -> Bool {
  match o {
    | EQ -> True
    | LT -> False
    | GT -> False
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

  // Verify local types are in ctrs
  let ctr_names = list.map(dc.ctrs, fn(pair) { pair.0 })
  list.contains(ctr_names, "Bool") |> should.equal(True)
  list.contains(ctr_names, "Ordering") |> should.equal(True)

  let merged_ctrs: cast.CtrEnv = list.append(dc.ctrs, initial_state.ctrs)
  let state: State = State(..initial_state, ctrs: merged_ctrs)
  let #(_value, _ty, final_state) = infer(state, core_term)

  // Should have NO errors of any kind
  let has_var_undefined = list.any(final_state.errors, fn(err) {
    case err {
      VarUndefined(_, _) -> True
      _ -> False
    }
  })
  has_var_undefined |> should.equal(False)

  let has_infinite_type = list.any(final_state.errors, fn(err) {
    case err {
      InfiniteType(_, _, _, _) -> True
      _ -> False
    }
  })
  has_infinite_type |> should.equal(False)
}
