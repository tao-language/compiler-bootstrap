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
/// ## Type Assumptions (TODO: Type-Directed Desugaring)
///
/// Currently, all binary operators are hardcoded to use I32 types:
/// - Arithmetic: `i32_add`, `i32_sub`, `i32_mul`, `i32_div`
/// - Comparison: `i32_eq`, `i32_neq`, `i32_lt`, etc.
/// - Logical: `i32_and`, `i32_or`, `i32_not`
///
/// This is a **temporary limitation**. Future work should implement:
/// 1. Type inference during desugaring
/// 2. Polymorphic Core terms with type-directed resolution
/// 3. Support for F32, F64, I64, U32, U64 types
///
/// See: [docs/plans/maintenance/06-code-quality-analysis.md](../../docs/plans/maintenance/06-code-quality-analysis.md)
///
/// For detailed documentation see:
/// - [Tao Overloading](../../docs/plans/tao/10-overloading-design.md)
/// - [Core Syntax](../../docs/core-syntax.md)
import tao/syntax.{type Expr, type BinOp, BinOp, type UnaryOp, UnaryOp, Int, Var as TaoVar, Add, Sub, Mul, Div, Eq, Neq, Lt, Gt, Lte, Gte, And, Or, Not, OverloadedFn, OverloadedApp, get_expr_span}
import core/core.{
  type Term, Lit, I32, Var, Call, Case, Match, Typ, Lam, Hole,
  type Literal, type LiteralType, type Case, type Pattern, I32T, I64T, F32T, F64T, U32T, U64T, PLitT, PAny,
}
import syntax/grammar.{type Span, Span}
import gleam/list
import gleam/option.{None}

// ============================================================================
// TYPE ASSUMPTIONS (TODO: Make configurable via type inference)
// ============================================================================

/// Default type for numeric literals and operations.
/// TODO: Infer from context during type checking.
const default_numeric_type = "i32"

/// Get the FFI operation name for a binary operator.
/// TODO: Make this type-directed (e.g., "f64_add" for floats).
fn binop_to_ffi(op: String) -> String {
  default_numeric_type <> "_" <> op
}

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
    TaoVar(name, span) -> desugar_var(name, span, ctx)
    BinOp(left, op, right, span) -> desugar_binop_expr(left, op, right, span, ctx)
    UnaryOp(op, expr, span) -> desugar_unary_op(op, expr, span, ctx)
    OverloadedFn(name, type_param, param_name, param_type, return_type, body, span) ->
      desugar_overloaded_fn(name, type_param, param_name, param_type, return_type, body, span)
    OverloadedApp(name, args, span) -> desugar_overloaded_app(name, args, span, ctx)
  }
}

/// Desugar binary operator expression.
fn desugar_binop_expr(left: Expr, op: BinOp, right: Expr, span: Span, ctx: DesugarCtx) -> Term {
  let op_name = case op {
    Add -> "add"
    Sub -> "sub"
    Mul -> "mul"
    Div -> "div"
    Eq -> "eq"
    Neq -> "neq"
    Lt -> "lt"
    Gt -> "gt"
    Lte -> "lte"
    Gte -> "gte"
    And -> "and"
    Or -> "or"
  }
  desugar_binop(left, right, span, ctx, op_name)
}

/// Desugar unary operator expression.
fn desugar_unary_op(op: UnaryOp, expr: Expr, span: Span, ctx: DesugarCtx) -> Term {
  case op {
    Not -> desugar_not(expr, span, ctx)
  }
}

// ============================================================================
// EXPRESSION DESUGARING
// ============================================================================

/// Desugar integer literal.
///
/// TODO: Infer numeric type from context (currently defaults to I32).
fn desugar_int(value: Int, span: Span) -> Term {
  Lit(I32(value), span)
}

/// Desugar variable reference.
fn desugar_var(name: String, span: Span, ctx: DesugarCtx) -> Term {
  case find_var(name, ctx.env) {
    Ok(index) -> Var(index, span)
    Error(_) -> {
      // Free variable - use index 0 (will be an error in type checking)
      Var(0, span)
    }
  }
}

/// Desugar binary operation.
///
/// TODO: Make type-directed by inferring operand types.
fn desugar_binop(
  left: Expr,
  right: Expr,
  span: Span,
  ctx: DesugarCtx,
  op: String,
) -> Term {
  let left_term = desugar_expr(left, ctx)
  let right_term = desugar_expr(right, ctx)
  Call(binop_to_ffi(op), [left_term, right_term], span)
}

/// Desugar logical NOT.
///
/// TODO: Make type-directed based on operand type.
fn desugar_not(expr: Expr, span: Span, ctx: DesugarCtx) -> Term {
  let expr_term = desugar_expr(expr, ctx)
  Call(binop_to_ffi("not"), [expr_term], span)
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
  let match_term = Match(
    Var(0, span),
    Typ(0, span),
    [
      Case(type_pattern, body_term, None, span),
      Case(PAny, body_term, None, span),  // Catch-all returns same body for simplicity
    ],
    span,
  )

  // Create lambda with implicit type param: %fn<T>(x) -> match T { ... }
  Lam([type_param], #(param_name, Hole(-1, span)), match_term, span)
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
        Call(name, [acc, arg], span)
      })
    }
    [] -> Var(0, span)  // No args
  }
}

/// Fold left over a list.
fn foldl(items: List(a), initial: b, func: fn(b, a) -> b) -> b {
  list.fold(items, initial, func)
}
