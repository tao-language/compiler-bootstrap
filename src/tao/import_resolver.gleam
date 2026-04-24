// Tao Import Resolver
// Resolves import statements in Tao modules.

import tao/ast.{type Module, type Stmt, Import, Module}
import syntax/span.{type Span, dummy}

// ============================================================================
// TAo IMPORT RESOLUTION
// ============================================================================

/// Resolve imports in a module
pub fn resolve_imports(module: Module) -> Result(Module, String) {
  case resolve_stmts(module.statements) {
    Ok(resolved) -> {
      let span = dummy()
      Ok(Module("unknown", resolved, span))
    }
    Error(e) -> Error(e)
  }
}

/// Resolve a list of statements
fn resolve_stmts(stmts: List(Stmt)) -> Result(List(Stmt), String) {
  case stmts {
    [] -> Ok([])
    [first, ..rest] -> {
      case resolve_stmt(first) {
        Ok(resolved) ->
          case resolve_stmts(rest) {
            Ok(rest_resolved) -> Ok([resolved, ..rest_resolved])
            Error(e) -> Error(e)
          }
        Error(e) -> Error(e)
      }
    }
  }
}

/// Resolve a single statement
fn resolve_stmt(stmt: Stmt) -> Result(Stmt, String) {
  case stmt {
    Import(path, _) -> {
      // Simplified: just validate the path
      Ok(Import(path, dummy()))
    }
    _ -> Ok(stmt)
  }
}
