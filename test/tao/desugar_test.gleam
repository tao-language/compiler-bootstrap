// ============================================================================
// TAO DESUGARER TESTS
// ============================================================================
/// Tests for Tao desugarer.
///
/// The desugarer converts Tao AST to core language terms.
import core/ast as core_ast
import core/state as state
import tao/desugar.{desugar_module, desugar_expr, desugar_stmt, type DesugarContext, DesugarContext}
import tao/global_context.{new_context, with_prelude}
import tao/language_config.{type LanguageConfig, default_config}
import gleeunit
import gleeunit/should
import syntax/grammar.{Span}
import gleam/list
import tao/ast.{Var, Lit, StmtExpr, Module as ModuleCtr, Int as TaoInt}

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// TEST HELPERS
// ============================================================================

const s1 = Span("desugar_test", 1, 1, 1, 1)

fn new_dc() -> DesugarContext {
  let gc = with_prelude(new_context())
  DesugarContext(gc, "test", [], [], [], [], default_config())
}

// ============================================================================
// BASIC DESUGARING TESTS
// ============================================================================

/// Test that desugar_expr returns a term for integer literal
pub fn desugar_int_literal_test() {
  let dc = new_dc()
  let lit_expr = Lit(TaoInt(42), s1)
  let #(term, _dc) = desugar_expr(lit_expr, dc)
  // Should produce a literal term
  case term {
    core_ast.Lit(_, _) -> True |> should.be_true()
    _ -> False |> should.be_true()
  }
}

/// Test that desugar_module returns a result
pub fn desugar_module_test() {
  let gc = with_prelude(new_context())
  let var_expr = Var("x", s1)
  let module = ModuleCtr("test", [StmtExpr(var_expr, s1)], s1)
  let #(_term, _dc) = desugar_module(module, gc)
  // Should produce a term (not crash)
  True |> should.be_true()
}

/// Test that desugar_stmt returns a result
pub fn desugar_stmt_test() {
  let dc = new_dc()
  let var_expr = Var("x", s1)
  let stmt = StmtExpr(var_expr, s1)
  let #(terms, _dc) = desugar_stmt(stmt, dc)
  // Should produce terms (not crash)
  let term_count = list.length(terms)
  term_count |> should.equal(1)
}
