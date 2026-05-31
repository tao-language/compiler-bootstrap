/// Core ctx — Type checking ctx, FFI, and error handling.
///
/// The `ctx` type carries all mutable ctx during type checking
/// and evaluation. It tracks variables, errors, holes, and FFI
/// definitions.
///
/// Errors accumulate as the type checker progresses, allowing
/// recovery after type errors.
import core/term.{type Term}
import core/utils
import core/value.{type Env, type Neut, type TypeVariant, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

// ============================================================================
// FFI
// ============================================================================

/// FFI entry — a builtin function that can be called from Core code.
///
/// The `impl` receives a list of #(value, type) pairs, where the type
/// is the result of type-checking the argument. This enables operator
/// overloading in Phase 5.
pub type FFI =
  List(#(String, fn(List(Value)) -> Option(Value)))

// ============================================================================
// CONTEXT
// ============================================================================

/// Type checking and evaluation ctx.
///
/// Context is threaded through every phase of the compiler. Fields:
///
/// * `env`: Values environment, used for eval
/// * `types`: Types environment, used for type inference and checking
/// * `subst`: Hole substitutions (hole_id → value)
/// * `errors`: Accumulated errors during type checking
/// * `ffi`: FFI builtin definitions available at runtime
/// * `hole_counter`: Next fresh hole ID
pub type Context {
  Context(
    env: Env,
    types: List(#(String, Value)),
    subst: Subst,
    errors: List(Error),
    ffi: FFI,
    hole_counter: Int,
  )
}

pub type Subst =
  List(#(Int, Value))

/// Type checking errors.
pub type Error {
  VarUndefined(name: String, span: Span)
  TypeMismatch(#(Value, Span), #(Value, Span))
  NeutralTypeMismatch(#(Neut, Span), #(Neut, Span))
  RcdFieldsMismatch(#(List(String), Span), #(List(String), Span))
  CallArityMismatch(#(Int, Span), #(Int, Span))
  InfiniteType(hole_id: Int, type_: Value, span: Span)
  NotAFunction(fun_type: Value, span: Span)
  TypeVariantUndefined(
    tag: #(String, Span),
    variants: #(List(TypeVariant), Span),
  )
  MatchMissing(patterns: List(String), covered: List(String), span: Span)
  MatchRedundant(span: Span)
  StepLimitExceeded(steps: Int, span: Span)
  CtorArgTypeMismatch(
    tag: String,
    expected_pattern: Value,
    actual_type: Value,
    span: Span,
  )
  CtorNotFound(tag: String, span: Span)
}

pub const new_ctx = Context([], [], [], [], [], 0)

pub fn lookup(ctx: Context, name: String) -> Option(#(Int, Value)) {
  lookup_loop(ctx.types, name, 0)
}

pub fn lookup_type_def(
  ctx: Context,
  name: String,
) -> Option(#(List(#(String, Value)), List(TypeVariant))) {
  case lookup_in_env(ctx, name) {
    Some(v.TypeDef(params, variants)) -> Some(#(params, variants))
    _ -> None
  }
}

fn lookup_in_env(ctx: Context, name: String) -> Option(Value) {
  case lookup(ctx, name) {
    Some(#(index, _)) -> utils.list_at(ctx.env, index)
    None -> None
  }
}

fn lookup_loop(
  types: List(#(String, Value)),
  name: String,
  index: Int,
) -> Option(#(Int, Value)) {
  case types {
    [] -> None
    [#(x, value), ..] if x == name -> Some(#(index, value))
    [_, ..types] -> lookup_loop(types, name, index + 1)
  }
}

pub fn with_err(ctx: Context, error: Error) -> Context {
  with_err_list(ctx, [error])
}

pub fn with_err_list(ctx: Context, errors: List(Error)) -> Context {
  Context(..ctx, errors: list.append(ctx.errors, errors))
}

pub fn new_hole(ctx: Context) -> #(Int, Context) {
  let id = ctx.hole_counter
  #(id, Context(..ctx, hole_counter: id + 1))
}

pub fn push_var(ctx: Context, var: #(String, Value, Value)) -> Context {
  let #(name, value, type_) = var
  Context(..ctx, env: [value, ..ctx.env], types: [#(name, type_), ..ctx.types])
}

pub fn push_var_list(
  ctx: Context,
  vars: List(#(String, Value, Value)),
) -> Context {
  let vars_env = list.map(vars, fn(var) { var.1 })
  let vars_types = list.map(vars, fn(var) { #(var.0, var.2) })
  Context(
    ..ctx,
    env: list.append(vars_env, ctx.env),
    types: list.append(vars_types, ctx.types),
  )
}

pub fn push_var_parameters(
  ctx: Context,
  params: List(#(String, Value)),
) -> Context {
  list.index_map(params, fn(param, index) {
    let #(name, type_) = param
    #(name, v.var(index), type_)
  })
  |> push_var_list(ctx, _)
}

pub fn pop_vars(ctx: Context, num_vars: Int) -> Context {
  Context(
    ..ctx,
    env: list.drop(ctx.env, num_vars),
    types: list.drop(ctx.types, num_vars),
  )
}
