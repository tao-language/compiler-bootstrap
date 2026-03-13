// ============================================================================
// TAO DESUGARER
// ============================================================================
/// Tao desugarer: transforms Tao AST to Core terms.
///
/// This module converts high-level Tao syntax to low-level Core terms.
/// For example:
/// - `x + y` becomes `%call i32_add(x, y)`
/// - `42` becomes Core literal
/// - `x` becomes Core variable
///
/// For detailed documentation see:
/// - [Tao MVP Plan](../../docs/plans/tao/09-tao-mvp-plan.md)
/// - [Core Syntax](../../docs/core-syntax.md)
import tao/syntax.{type MvpExpr, MvpInt, MvpVar, MvpAdd, MvpSub, MvpMul, MvpDiv, get_expr_span}
import core/core.{
  type Term, Term, Lit, I32, Var, Call,
  type Literal, type LiteralType, I32T,
}
import syntax/grammar.{type Span, Span}

// ============================================================================
// DESUGAR CONTEXT
// ============================================================================

/// Context for desugaring.
///
/// Tracks:
/// - Variable environment (name → De Bruijn index)
/// - Current span for error reporting
pub type DesugarCtx {
  DesugarCtx(
    env: List(#(String, Int)),  // Variable name → De Bruijn index
    next_index: Int,             // Next available De Bruijn index
    span: Span,                  // Current source span
  )
}

/// Create initial desugar context.
pub fn initial_ctx(span: Span) -> DesugarCtx {
  DesugarCtx(env: [], next_index: 0, span: span)
}

// ============================================================================
// MAIN DESUGAR FUNCTION
// ============================================================================

/// Desugar Tao expression to Core term.
///
/// This is the main entry point for desugaring.
pub fn desugar(expr: MvpExpr) -> Term {
  desugar_expr(expr, initial_ctx(get_expr_span(expr)))
}

/// Desugar expression with context.
fn desugar_expr(expr: MvpExpr, ctx: DesugarCtx) -> Term {
  case expr {
    MvpInt(value, span) -> desugar_int(value, span)
    MvpVar(name, span) -> desugar_var(name, span, ctx)
    MvpAdd(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_add")
    MvpSub(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_sub")
    MvpMul(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_mul")
    MvpDiv(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_div")
  }
}

// ============================================================================
// EXPRESSION DESUGARING
// ============================================================================

/// Desugar integer literal.
fn desugar_int(value: Int, span: Span) -> Term {
  Term(Lit(I32(value)), span)
}

/// Desugar variable reference.
fn desugar_var(name: String, span: Span, ctx: DesugarCtx) -> Term {
  case find_var(name, ctx.env) {
    Ok(index) -> Term(Var(index), span)
    Error(_) -> {
      // Free variable - use index 0 (will be an error in type checking)
      Term(Var(0), span)
    }
  }
}

/// Desugar binary operation.
fn desugar_binop(
  left: MvpExpr,
  right: MvpExpr,
  span: Span,
  ctx: DesugarCtx,
  op_name: String,
) -> Term {
  let left_term = desugar_expr(left, ctx)
  let right_term = desugar_expr(right, ctx)
  Term(Call(op_name, [left_term, right_term]), span)
}

// ============================================================================
// ENVIRONMENT HELPERS
// ============================================================================

/// Find variable in environment.
fn find_var(name: String, env: List(#(String, Int))) -> Result(Int, Nil) {
  case env {
    [] -> Error(Nil)
    [pair, ..rest] -> {
      let #(n, i) = pair
      case n == name {
        True -> Ok(i)
        False -> find_var(name, rest)
      }
    }
  }
}

/// Add variable to environment.
fn add_var(name: String, ctx: DesugarCtx) -> DesugarCtx {
  DesugarCtx(
    env: [#(name, ctx.next_index), ..ctx.env],
    next_index: ctx.next_index + 1,
    span: ctx.span,
  )
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Merge two spans.
fn merge_spans(left: Span, right: Span) -> Span {
  Span(
    file: left.file,
    start_line: left.start_line,
    start_col: left.start_col,
    end_line: right.end_line,
    end_col: right.end_col,
  )
}
