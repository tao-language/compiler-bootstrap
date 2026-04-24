// Tao Syntax - Minimal parser for the Tao language
// Simplified implementation for the prototype stage.

import syntax/span
import tao/ast.{type Expr, type Module, Module, Var}

/// Parse a Tao expression from source code
pub fn parse_expr(_source: String) -> Result(Expr, String) {
  // Simplified: just return a placeholder
  Ok(Var("placeholder", span.dummy()))
}

/// Parse Tao source code (returns statements)
pub fn parse(_source: String) -> Result(Module, List(String)) {
  // Simplified: just return an empty module
  Ok(Module("main", [], span.dummy()))
}
