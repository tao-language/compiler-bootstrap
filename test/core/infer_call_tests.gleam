// ============================================================================
// INFER CALL TESTS
// ============================================================================
/// Tests for the infer_call function and related inference.
///
/// These tests verify that eq with concrete literals returns Bool type,
/// and that infer handles a simple application correctly.
import core/ast as ast
import core/state as state
import core/infer as infer
import tao/ffi.{ffi_eq}
import syntax/grammar as g
import gleam/option.{type Option, None, Some}
import gleeunit
import gleeunit/should

pub fn main() {
  test_infer_call_eq_with_literals()
  test_infer_call_eq_with_variables()
  test_infer_simple_app()
}

fn test_infer_call_eq_with_literals() {
  // Test that eq with concrete literals returns Bool type
  let args = [
    ast.VLit(ast.IntLit(10)),
    ast.VLit(ast.IntLit(10)),
  ]
  
  // Call ffi_eq directly
  let result = ffi_eq(args)
  case result {
    Some(val) -> case val {
      ast.VCtrValue(ast.VCtr("True", ast.VUnit)) -> {
        // OK - test passes
      }
      other -> {
        let val_str = case other {
          ast.VCtrValue(ast.VCtr(tag, _)) -> "VCtr(" <> tag <> ")"
          _ -> "other"
        }
        panic("Expected True for 10 == 10, got: " <> val_str)
      }
    }
    None -> panic("Expected Some result")
  }
}

fn test_infer_call_eq_with_variables() {
  // Test that eq with variables returns None (non-concrete)
  let args = [
    ast.VCall("x", []),
    ast.VLit(ast.IntLit(10)),
  ]
  
  let result = ffi_eq(args)
  case result {
    Some(_) -> panic("Expected None for non-literal args")
    None -> panic("Expected Error for non-literal args")
  }
}

fn test_infer_simple_app() {
  // Test that infer handles a simple application correctly
  let span = g.Span("", 0, 0, 0, 0)
  let s = state.State(..state.initial_state, errors: [], subst: [], level: 0, hole_counter: 0)
  
  // Simple identity function: λx.x applied to 10
  let body = ast.Var(0, span)
  let lam = ast.Lam([], #("x", ast.Hole(-1, span)), body, span)
  let app = ast.App(lam, [], ast.Lit(ast.IntLit(10), span), span)
  
  let #(val, ty, s) = infer.infer(s, app)
  
  // The result should be a value, not VErr
  case val {
    ast.VErr -> panic("Expected non-error value")
    _ -> {
      // The type should be ILitT (the type of the argument)
      case ty {
        ast.VLitT(ast.ILitT) -> {
          // OK - test passes
        }
        other -> {
          let ty_str = case other {
            ast.VLitT(lit) -> case lit {
              ast.ILitT -> "ILitT"
              ast.I32T -> "I32T"
              _ -> "other"
            }
            _ -> "other"
          }
          panic("Expected ILitT type, got: " <> ty_str)
        }
      }
    }
  }
}
