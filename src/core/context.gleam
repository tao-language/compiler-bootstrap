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
import core/value.{
  type Env, type Neut, type TypeDefinition, type Value, type Variant,
} as v
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
  NotAFunction(fun: Term, fun_type: Value, span: Span)
  AppExpectedExplicitArg(fun_type: Value, span: Span)
  TypeVariantUndefined(
    tag: #(String, Span),
    variants: #(List(#(String, Variant)), Span),
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
    Some(#(index, _)) -> utils.list_at(ctx.env, index)
    None -> None
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
        #(v.hole(id), ctx)
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
// pub fn instantiate_holes(ctx: Context, value: Value) -> #(Value, Context) {
//   case value {
//     v.Typ(_) -> #(value, ctx)
//     v.Lit(_) -> #(value, ctx)
//     v.LitT(_) -> #(value, ctx)
//     v.Ctr(tag, arg) -> {
//       let #(arg, ctx) = instantiate_holes(ctx, arg)
//       #(v.Ctr(tag, arg), ctx)
//     }
//     v.Rcd(fields) -> {
//       let #(fields, ctx) =
//         list.fold(fields, #([], ctx), fn(acc, kv) {
//           let #(#(fields, ctx), #(name, value)) = #(acc, kv)
//           let #(value, ctx) = instantiate_holes(ctx, value)
//           #([#(name, value), ..fields], ctx)
//         })
//       #(v.Rcd(fields), ctx)
//     }
//     v.RcdT(fields) -> {
//       let #(fields, ctx) =
//         list.fold(fields, #([], ctx), fn(acc, kv) {
//           let #(#(fields, ctx), #(name, #(value, maybe_default))) = #(acc, kv)
//           let #(value, ctx) = instantiate_holes(ctx, value)
//           let #(maybe_default, ctx) = case maybe_default {
//             Some(value) -> {
//               let #(value, ctx) = instantiate_holes(ctx, value)
//               #(Some(value), ctx)
//             }
//             None -> #(None, ctx)
//           }
//           #([#(name, #(value, maybe_default)), ..fields], ctx)
//         })
//       #(v.RcdT(fields), ctx)
//     }
//     v.Neut(neutral) ->
//       case neutral {
//         v.NVar(_) -> #(value, ctx)
//         v.NHole(id) if id < 0 -> {
//           let #(id, ctx) = new_hole(ctx)
//           #(v.hole(id), ctx)
//         }
//         v.NHole(_) -> #(value, ctx)
//         v.NApp(fun:, arg:) -> todo
//         v.NMatch(env:, arg:, cases:) -> todo
//         v.NCall(name:, args:) -> todo
//       }
//     v.Lam(env:, param:, body:) -> todo
//     v.Pi(env:, implicit:, domain:, codomain:) -> todo
//     v.Fix(env:, name:, body:) -> todo
//     v.TypeDef(env:, type_def:) -> todo
//     v.Err -> todo
//   }
// }
