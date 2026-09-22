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
import core/step.{step}
import core/value.{type Env, type Type, type TypeDefinition, type Value} as v
import gleam/list
import gleam/option.{type Option, None, Some}
import syntax/span.{type Span}

// ============================================================================
// CONTEXT
// ============================================================================

/// Type checking and evaluation ctx.
///
/// Context is threaded through every phase of the compiler. Fields:
///
/// * `env`: Values environment, used for eval
/// * `types`: Types environment, used for type inference and checking
/// * `subst`: Hole substitutions (hole_id → (captured_env, solution value))
/// * `errors`: Accumulated errors during type checking
/// * `trace`: Breadcrumb labels for error reporting (innermost first)
/// * `ffi`: FFI builtin definitions available at runtime
/// * `hole_counter`: Next fresh hole ID
/// * `deferred`: Constraints that could not be decided while a side was
///   still neutral; retried as holes get solved and discharged when the
///   context is resolved (`resolve.context`).
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
    deferred: Deferred,
  )
}

/// A hole substitution: `hole_id → (captured_env, solution)`. The
/// captured environment is the frame current when the hole was solved;
/// the solution's `NVar` levels are relative to it, so it must be kept
/// to quote the solution back into a term (see `resolve.term`).
pub type Subst =
  List(#(Int, #(Env, Value)))

/// A deferred unification constraint: a pair that the unifier met while
/// at least one side was neutral and could not be decided yet.
pub type Deferred =
  List(#(#(Value, Span), #(Value, Span)))

pub const new_ctx = Context([], [], [], [], [], [], 0, [])

/// Look up a variable by name, returning its index (innermost-first)
/// and type. Only the first (innermost) binding is found.
pub fn lookup(ctx: Context, name: String) -> Option(#(Int, Value)) {
  step("context:lookup")
  lookup_loop(ctx.types, name, 0)
}

fn lookup_loop(
  types: List(#(String, Value)),
  name: String,
  index: Int,
) -> Option(#(Int, Value)) {
  step("context:lookup_loop")
  case types {
    [] -> None
    [#(x, value), ..] if x == name -> Some(#(index, value))
    [_, ..types] -> lookup_loop(types, name, index + 1)
  }
}

/// Look up a type definition by name, returning its captured
/// environment (so its parameters are addressable) and the definition.
/// The name is first looked up in the environment (local bindings); if
/// not found there, the module records in the environment are searched,
/// since type constructor applications are tags (not variables) and so
/// never bring a module member into scope as a local binding. This is
/// how prelude type definitions (e.g. `Bool` in `lib/prelude`) become
/// visible to every module.
pub fn lookup_type_def(
  ctx: Context,
  name: String,
) -> Option(#(Env, TypeDefinition)) {
  step("context:lookup_type_def")
  case lookup_in_env(ctx, name) {
    Some(v.TypeDef(env, type_def)) -> Some(#(env, type_def))
    Some(_) -> None
    None -> lookup_in_modules(ctx, name)
  }
}

/// Search the module records of the environment for a definition of
/// `name`. A module record is a closed record whose fields are
/// `(name, #(value, default))` pairs.
fn lookup_in_modules(
  ctx: Context,
  name: String,
) -> Option(#(Env, TypeDefinition)) {
  step("context:lookup_in_modules")
  list.fold(ctx.env, None, fn(acc, val) {
    case acc, val {
      Some(found), _ -> Some(found)
      None, v.Rcd(fields, None) ->
        case list.key_find(fields, name) {
          Ok(#(v.TypeDef(env, type_def), _)) -> Some(#(env, type_def))
          _ -> None
        }
      None, _ -> None
    }
  })
}

fn lookup_in_env(ctx: Context, name: String) -> Option(Value) {
  step("context:lookup_in_env")
  case lookup_var(ctx, name) {
    Some(#(val, _)) -> Some(val)
    None -> None
  }
}

/// Look up a variable by name, returning both its value and its type.
pub fn lookup_var(ctx: Context, name: String) -> Option(#(Value, Type)) {
  step("context:lookup_var")
  case ctx.types, ctx.env {
    [#(x, typ), ..], [val, ..] if x == name -> Some(#(val, typ))
    [_, ..types], [_, ..env] -> {
      let ctx = Context(..ctx, env: env, types: types)
      lookup_var(ctx, name)
    }
    _, _ -> None
  }
}

/// Bind `name` to a new value/type, replacing the first (innermost)
/// matching binding *in place* (preserving its position, so de Bruijn
/// levels of other variables stay valid), or appending at the outermost
/// end if the name is new.
pub fn set_var(ctx: Context, name: String, value: Value, typ: Type) -> Context {
  step("context:set_var")
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
  step("context:with_err")
  let err = Error(err_data, span, list.reverse(ctx.trace))
  Context(..ctx, errors: list.unique([err, ..ctx.errors]))
}

/// Allocate a fresh hole ID.
pub fn new_hole(ctx: Context) -> #(Int, Context) {
  step("context:new_hole")
  let id = ctx.hole_counter
  #(id, Context(..ctx, hole_counter: id + 1))
}

/// Push a (name, value, type) binding as the new innermost scope.
pub fn push_var(ctx: Context, var: #(String, Value, Value)) -> Context {
  step("context:push_var")
  let #(name, val, typ) = var
  Context(..ctx, env: [val, ..ctx.env], types: [#(name, typ), ..ctx.types])
}

/// Push a binding where the value and/or type may be unknown, in which
/// case a fresh (unsolved) hole is used as a placeholder to be solved by
/// unification later.
pub fn push_var_opt(
  ctx: Context,
  var: #(String, Option(Value), Option(Value)),
) -> Context {
  step("context:push_var_opt")
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
  step("context:push_var_opt_list")
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
  step("context:pop_vars")
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
  step("context:push_trace")
  Context(..ctx, trace: [trace, ..ctx.trace])
}

pub fn pop_trace(ctx: Context) -> Context {
  step("context:pop_trace")
  case ctx.trace {
    [_, ..trace] -> Context(..ctx, trace: trace)
    [] -> ctx
  }
}
