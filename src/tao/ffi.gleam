// Tao FFI - Built-in functions
// Defines the FFI functions available in Tao.

import core/ast.{TPi, TVar, IntVal}
import core/state.{type FfiEntry, FfiEntry}


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
