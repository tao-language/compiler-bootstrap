/// Core ctx — Type checking ctx, FFI, and error handling.
///
/// The `ctx` type carries all mutable ctx during type checking
/// and evaluation. It tracks variables, errors, holes, and FFI
/// definitions.
///
/// Errors accumulate as the type checker progresses, allowing
/// recovery after type errors.
import core/error.{type Error, type ErrorData, Error}
import core/ffi.{type FFI}
import core/value.{type Env, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}
import utils/list_utils.{list_at}

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
    trace: List(#(String, Span)),
    ffi: FFI,
    hole_counter: Int,
  )
}

pub type Subst =
  List(#(Int, Value))

pub const new_ctx = Context([], [], [], [], [], [], 0)

pub fn lookup(ctx: Context, name: String) -> Option(#(Int, Value)) {
  lookup_loop(ctx.types, name, 0)
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

pub fn lookup_type_def(
  ctx: Context,
  name: String,
) -> Option(#(Env, TypeDefinition)) {
  case lookup_in_env(ctx, name) {
    Some(v.TypeDef(env, type_def)) -> Some(#(env, type_def))
    _ -> None
  }
}

fn lookup_in_env(ctx: Context, name: String) -> Option(Value) {
  case lookup(ctx, name) {
    Some(#(index, _)) -> list_at(ctx.env, index)
    None -> None
  }
}

pub fn with_err(ctx: Context, err_data: ErrorData, span: Span) -> Context {
  let err = Error(err_data, span, list.reverse(ctx.trace))
  Context(..ctx, errors: list.unique([err, ..ctx.errors]))
}

pub fn new_hole(ctx: Context) -> #(Int, Context) {
  let id = ctx.hole_counter
  #(id, Context(..ctx, hole_counter: id + 1))
}

pub fn new_hole_list(ctx: Context, num_holes: Int) -> #(List(Int), Context) {
  case num_holes > 0 {
    True -> {
      let #(hole_id, ctx) = new_hole(ctx)
      let #(holes, ctx) = new_hole_list(ctx, num_holes - 1)
      #([hole_id, ..holes], ctx)
    }
    False -> #([], ctx)
  }
}

pub fn push_var(
  ctx: Context,
  var: #(String, Option(Value), Option(Value)),
) -> Context {
  let #(name, maybe_value, maybe_type) = var
  let instantiate = fn(ctx, maybe_value) {
    case maybe_value {
      Some(value) -> #(value, ctx)
      None -> {
        let #(id, ctx) = new_hole(ctx)
        #(v.hole(ctx.env, Some(id)), ctx)
      }
    }
  }
  let #(value, ctx) = instantiate(ctx, maybe_value)
  let #(type_, ctx) = instantiate(ctx, maybe_type)
  Context(..ctx, env: [value, ..ctx.env], types: [#(name, type_), ..ctx.types])
}

pub fn push_var_list(
  ctx: Context,
  vars: List(#(String, Option(Value), Option(Value))),
) -> Context {
  case vars {
    [] -> ctx
    [var, ..vars] -> {
      let ctx = push_var(ctx, var)
      push_var_list(ctx, vars)
    }
  }
}

pub fn pop_vars(ctx: Context, num_vars: Int) -> Context {
  Context(
    ..ctx,
    env: list.drop(ctx.env, num_vars),
    types: list.drop(ctx.types, num_vars),
  )
}

// ============================================================================
// ERROR TRACE
// ============================================================================

pub fn push_trace(ctx: Context, trace: #(String, Span)) -> Context {
  Context(..ctx, trace: [trace, ..ctx.trace])
}

pub fn pop_trace(ctx: Context) -> Context {
  case ctx.trace {
    [_, ..trace] -> Context(..ctx, trace: trace)
    [] -> ctx
  }
}
