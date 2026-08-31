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
import core/value.{type Env, type Type, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}
import utils/list_utils.{at}

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
/// * `trace`: Breadcrumb labels for error reporting (innermost first)
/// * `ffi`: FFI builtin definitions available at runtime
/// * `hole_counter`: Next fresh hole ID
///
/// Invariant: `env` and `types` always have the same length and the same
/// order (innermost first); `lookup` returns an index valid for *both*.
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

/// Look up a variable by name, returning its index (innermost-first)
/// and type. Only the first (innermost) binding is found.
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

/// Look up a type definition by name, returning its captured
/// environment (so its parameters are addressable) and the definition.
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
    Some(#(index, _)) -> at(ctx.env, index)
    None -> None
  }
}

/// Look up a variable by name, returning both its value and its type.
pub fn lookup_var(ctx: Context, name: String) -> Option(#(Value, Type)) {
  case ctx.types, ctx.env {
    [#(x, typ), ..], [val, ..] if x == name -> Some(#(val, typ))
    [_, ..types], [_, ..env] -> {
      let ctx = Context(..ctx, env: env, types: types)
      lookup_var(ctx, name)
    }
    _, _ -> None
  }
}

/// Bind `name` to a new value/type, replacing an existing binding *in
/// place* (preserving its position, so de Bruijn levels of other
/// variables stay valid) or prepending if the name is new.
pub fn set_var(ctx: Context, name: String, value: Value, typ: Type) -> Context {
  case ctx.types, ctx.env {
    [#(x, _), ..types], [_, ..env] if x == name ->
      Context(..ctx, env: [value, ..env], types: [#(name, typ), ..types])
    [first_typ, ..types], [first_val, ..env] -> {
      let ctx = Context(..ctx, env: env, types: types)
      let ctx = set_var(ctx, name, value, typ)
      Context(..ctx, env: [first_val, ..ctx.env], types: [
        first_typ,
        ..ctx.types
      ])
    }
    _, _ ->
      Context(..ctx, env: [value, ..ctx.env], types: [#(name, typ), ..ctx.types])
  }
}

/// Record an error, tagged with the current trace. Identical errors
/// (same data, span and trace) are deduplicated.
pub fn with_err(ctx: Context, err_data: ErrorData, span: Span) -> Context {
  let err = Error(err_data, span, list.reverse(ctx.trace))
  Context(..ctx, errors: list.unique([err, ..ctx.errors]))
}

/// Allocate a fresh hole ID.
pub fn new_hole(ctx: Context) -> #(Int, Context) {
  let id = ctx.hole_counter
  #(id, Context(..ctx, hole_counter: id + 1))
}

/// Allocate `num_holes` fresh hole IDs at once.
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

/// Push a (name, value, type) binding as the new innermost scope.
pub fn push_var(ctx: Context, var: #(String, Value, Value)) -> Context {
  let #(name, val, typ) = var
  Context(..ctx, env: [val, ..ctx.env], types: [#(name, typ), ..ctx.types])
}

pub fn push_var_list(
  ctx: Context,
  vars: List(#(String, Value, Value)),
) -> Context {
  case vars {
    [] -> ctx
    [var, ..vars] -> {
      let ctx = push_var(ctx, var)
      push_var_list(ctx, vars)
    }
  }
}

/// Push a binding where the value and/or type may be unknown, in which
/// case a fresh (unsolved) hole is used as a placeholder to be solved by
/// unification later.
pub fn push_var_opt(
  ctx: Context,
  var: #(String, Option(Value), Option(Value)),
) -> Context {
  let #(name, maybe_value, maybe_type) = var
  let instantiate = fn(ctx, maybe_value) {
    case maybe_value {
      Some(value) -> #(value, ctx)
      None -> {
        let #(id, ctx) = new_hole(ctx)
        #(v.hole(ctx.env, id), ctx)
      }
    }
  }
  let #(val, ctx) = instantiate(ctx, maybe_value)
  let #(typ, ctx) = instantiate(ctx, maybe_type)
  push_var(ctx, #(name, val, typ))
}

/// `push_var_opt` applied to a list of bindings, innermost first.
pub fn push_var_opt_list(
  ctx: Context,
  vars: List(#(String, Option(Value), Option(Value))),
) -> Context {
  case vars {
    [] -> ctx
    [var, ..vars] -> {
      let ctx = push_var_opt(ctx, var)
      push_var_opt_list(ctx, vars)
    }
  }
}

/// Drop the innermost `num_vars` bindings (value and type together).
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

/// Push a breadcrumb label, used to report which construct an error
/// occurred inside.
pub fn push_trace(ctx: Context, trace: #(String, Span)) -> Context {
  Context(..ctx, trace: [trace, ..ctx.trace])
}

pub fn pop_trace(ctx: Context) -> Context {
  case ctx.trace {
    [_, ..trace] -> Context(..ctx, trace: trace)
    [] -> ctx
  }
}
