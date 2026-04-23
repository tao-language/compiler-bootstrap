// ============================================================================
// CORE INFER UTILITIES
// Shared helper functions for type inference.
// Used by infer.gleam and other core modules.
// ============================================================================
import core/ast as ast

/// Coerce a term to a specific type.
/// Used when a type annotation is explicit.
pub fn coerce_to_type(term: ast.Term, target: ast.Value) -> ast.Term {
  case target {
    ast.VNeut(ast.HHole(_), _) -> term  // Holes accept any term
    _ -> term  // For known types, accept as-is (full coercion is in infer)
  }
}

/// Check if a value is the truth constructor.
pub fn is_truth_value(value: ast.Value, truth_ctor: String) -> Bool {
  ast.is_true_value(value, truth_ctor)
}

/// Check if two type annotations are equal (for equality checking in inference).
pub fn types_equal(t1: ast.Value, t2: ast.Value) -> Bool {
  t1 == t2
}

/// Check if a value is a hole (unresolved variable).
pub fn is_hole_value(v: ast.Value) -> Bool {
  case v {
    ast.VNeut(ast.HHole(_), _) -> True
    _ -> False
  }
}

/// Check if a value is a variable (HVar) - used during type inference.
pub fn is_var_value(v: ast.Value) -> Bool {
  case v {
    ast.VNeut(ast.HVar(_), _) -> True
    _ -> False
  }
}

/// Check if a value is an unresolved hole or a variable.
pub fn is_unresolved(v: ast.Value) -> Bool {
  case v {
    ast.VNeut(ast.HHole(_), _) -> True
    ast.VNeut(ast.HVar(_), _) -> True
    _ -> False
  }
}

/// Get variable level from a variable value (if it's an HVar).
/// Returns Ok(level) if value is a HVar, Error(Nil) otherwise.
pub fn get_var_level(v: ast.Value) -> Result(Int, Nil) {
  case v {
    ast.VNeut(ast.HVar(lvl), _) -> Ok(lvl)
    _ -> Error(Nil)
  }
}

/// Check if a value is a literal type value (VLitT).
pub fn is_lit_t(v: ast.Value) -> Bool {
  case v {
    ast.VLitT(_) -> True
    _ -> False
  }
}
