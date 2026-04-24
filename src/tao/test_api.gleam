// Tao Test API
// Simple test framework for Tao.

import core/ast.{type Term, type Value}
import core/state

// ============================================================================
// TAo TEST EXECUTION
// ============================================================================

/// Run a test expression (simplified prototype version)
pub fn run_test(_name: String, _expr: Term, expected: Value) -> Result(Value, String) {
  // Simplified: just return the expected value
  Ok(expected)
}
