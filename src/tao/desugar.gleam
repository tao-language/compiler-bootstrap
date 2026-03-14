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
/// - [Tao Overloading](../../docs/plans/tao/10-overloading-design.md)
/// - [Core Syntax](../../docs/core-syntax.md)
import tao/syntax.{type Expr, Int, Var, Add, Sub, Mul, Div, Eq, Neq, Lt, Gt, Lte, Gte, And, Or, Not, OverloadedFn, OverloadedApp, get_expr_span}
import core/core.{
  type Term, Term, Lit, I32, Var as CoreVar, Call, Case, Match, Typ, Lam, Hole,
  type Literal, type LiteralType, type Case, type Pattern, I32T, I64T, F32T, F64T, U32T, U64T, PLitT, PAny,
}
import syntax/grammar.{type Span, Span}
import gleam/list
import gleam/option.{None}

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
pub fn desugar(expr: Expr) -> Term {
  desugar_expr(expr, initial_ctx(get_expr_span(expr)))
}

/// Desugar expression with context.
fn desugar_expr(expr: Expr, ctx: DesugarCtx) -> Term {
  case expr {
    Int(value, span) -> desugar_int(value, span)
    Var(name, span) -> desugar_var(name, span, ctx)
    Add(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_add")
    Sub(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_sub")
    Mul(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_mul")
    Div(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_div")
    Eq(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_eq")
    Neq(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_neq")
    Lt(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_lt")
    Gt(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_gt")
    Lte(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_lte")
    Gte(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_gte")
    And(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_and")
    Or(left, right, span) -> desugar_binop(left, right, span, ctx, "i32_or")
    Not(expr, span) -> desugar_not(expr, span, ctx)
    OverloadedFn(name, type_param, param_name, param_type, return_type, body, span) ->
      desugar_overloaded_fn(name, type_param, param_name, param_type, return_type, body, span)
    OverloadedApp(name, args, span) -> desugar_overloaded_app(name, args, span, ctx)
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
    Ok(index) -> Term(CoreVar(index), span)
    Error(_) -> {
      // Free variable - use index 0 (will be an error in type checking)
      Term(CoreVar(0), span)
    }
  }
}

/// Desugar binary operation.
fn desugar_binop(
  left: Expr,
  right: Expr,
  span: Span,
  ctx: DesugarCtx,
  op_name: String,
) -> Term {
  let left_term = desugar_expr(left, ctx)
  let right_term = desugar_expr(right, ctx)
  Term(Call(op_name, [left_term, right_term]), span)
}

/// Desugar logical NOT.
fn desugar_not(expr: Expr, span: Span, ctx: DesugarCtx) -> Term {
  let expr_term = desugar_expr(expr, ctx)
  Term(Call("i32_not", [expr_term]), span)
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

// ============================================================================
// OVERLOADING DESUGARING
// ============================================================================

/// Desugar overloaded function definition to Core.
///
/// Tao: fn (+)(x: I32) -> I32 { x + 1 }
/// Core: %let (+) = %fn<T>(x) -> %match T { | %I32 -> %call i32_add(x, 1) }
///
/// The implicit type parameter enables type-directed dispatch at compile time.
/// Type matching happens during type inference, and the appropriate implementation
/// is selected based on the concrete type.
fn desugar_overloaded_fn(
  _name: String,
  type_param: String,
  param_name: String,
  param_type: String,
  _return_type: String,
  body: Expr,
  span: Span,
) -> Term {
  // Desugar the body expression
  let body_term = desugar_expr(body, initial_ctx(span))

  // Create match expression: %match T { | %Type -> body }
  let type_pattern = type_to_pattern(param_type)
  let match_term = Term(
    Match(
      Term(CoreVar(0), span),
      Term(Typ(0), span),
      [
        Case(type_pattern, body_term, None, span),
        Case(PAny, body_term, None, span),  // Catch-all returns same body for simplicity
      ],
    ),
    span,
  )

  // Create lambda with implicit type param: %fn<T>(x) -> match T { ... }
  Term(Lam([type_param], #(param_name, Term(Hole(-1), span)), match_term), span)
}

/// Convert type name to pattern for matching.
fn type_to_pattern(type_name: String) -> Pattern {
  case type_name {
    "I32" -> PLitT(I32T)
    "I64" -> PLitT(I64T)
    "F32" -> PLitT(F32T)
    "F64" -> PLitT(F64T)
    "U32" -> PLitT(U32T)
    "U64" -> PLitT(U64T)
    _ -> PAny  // Default case for unknown types
  }
}

/// Desugar overloaded function application.
///
/// Tao: (+)(1, 2)
/// Core: %call (+)(1, 2)  -- type inferred during type checking
fn desugar_overloaded_app(
  name: String,
  args: List(Expr),
  span: Span,
  ctx: DesugarCtx,
) -> Term {
  // Desugar all arguments
  let arg_terms = list.map(args, fn(arg) { desugar_expr(arg, ctx) })

  // Create function call (implicit args will be filled during type inference)
  case arg_terms {
    [first, ..rest] -> {
      // For now, create a simple call
      // Type inference will add implicit type args
      foldl(rest, first, fn(acc, arg) {
        Term(Call(name, [acc, arg]), span)
      })
    }
    [] -> Term(CoreVar(0), span)  // No args
  }
}

/// Fold left over a list.
fn foldl(items: List(a), initial: b, func: fn(b, a) -> b) -> b {
  list.fold(items, initial, func)
}
