// Tao FFI - Built-in functions
// Defines the FFI functions available in Tao.

import core/ast.{type Type, TPi, TVar, IntLit, FloatLit, StringLit, Var, Lam, App, PatternConstr, PatternVar, Match, MatchCase, PatVar, IntVal, FloatVal, StringVal, Closure}
import core/state.{type FfiEntry, FfiEntry}
import gleam/list

// ============================================================================
// TAo FFI BUILTINS
// ============================================================================

/// Get all FFI builtins
pub fn builtins() -> List(FfiEntry) {
  [
    FfiEntry(
      name: "+",
      typ: TPi("Int", TPi("Int", TVar(0), TVar(0)), TVar(0)),
      args: [TVar(0), TVar(0)],
      impl: fn(args) {
        case args {
          [IntVal(a), IntVal(b)] -> IntVal(a + b)
          _ -> IntVal(0)
        }
      },
    ),
  ]
}
