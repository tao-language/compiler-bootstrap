/// Module Definition — two-phase type checking of Tao modules
///
/// `types` runs first over all modules, creating the module records.
/// Functions and type definitions are evaluated eagerly (their values
/// are concrete from the start); other definitions are registered as
/// unsolved holes. `values` then infers each definition that is still
/// a hole and unifies it with that hole. Because every module record
/// exists before any body is checked, definitions may reference each
/// other — including across modules — in any order.
import core/ast as core
import core/context.{type Context, lookup_type_def}
import core/error as e
import core/eval.{eval}
import core/infer.{check, infer}
import core/step.{step}
import core/unify.{unify}
import core/value as v
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string
import tao/ast.{type Stmt} as tao
import tao/declare.{type ModName, type Name}
import tao/desugar
import utils/list_utils

/// Phase 1: register every definition, creating the module records.
/// Returns the context with all modules in scope.
pub fn types(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> Context {
  list.fold(defs, ctx, fn(ctx, def) {
    let #(mod_name, mod_defs) = def
    let shadowed = shadowed_imports(mod_defs)
    list.fold(mod_defs, ctx, fn(ctx, mod_def) {
      let #(name, stmt) = mod_def
      case shadowed_import(name, stmt, shadowed) {
        True -> ctx
        False -> {
          let #(_, _, ctx) = type_stmt(ctx, defs, mod_name, name, stmt)
          ctx
        }
      }
    })
  })
}

/// Phase 2: infer each definition whose value is still an unsolved
/// hole from phase 1, and unify the result with that hole. Definitions
/// are processed in module order; ordering does not affect the
/// *solvability* of holes (all constraints are accumulated) but can
/// affect error reporting.
pub fn values(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
) -> Context {
  list.fold(defs, ctx, fn(ctx, def) {
    let #(mod_name, mod_defs) = def
    let shadowed = shadowed_imports(mod_defs)
    list.fold(mod_defs, ctx, fn(ctx, mod_def) {
      let #(name, stmt) = mod_def
      case shadowed_import(name, stmt, shadowed) {
        True -> ctx
        False ->
          case get_var(ctx, mod_name, name) {
            Some(#(v.Neut(v.NHole(..)) as hole, typ)) -> {
              let s = stmt.span
              let #(val, _, ctx) =
                stmt_value(ctx, defs, mod_name, name, stmt, Some(typ))
              unify(ctx, #(val, s), #(hole, s))
            }
            _ -> ctx
          }
      }
    })
  })
}

/// The names of a module's *local* definitions (everything but imports
/// and tests). A local definition shadows an imported name of the same
/// module, so the import entry must not be registered or inferred on its
/// own: it would share the module record's single entry for the name and
/// the import's value (the imported module's record) would be unified
/// with the local definition's hole.
fn shadowed_imports(mod_defs: List(#(Name, Stmt))) -> List(Name) {
  list.flat_map(mod_defs, fn(entry) {
    let #(name, stmt) = entry
    case stmt.data {
      tao.Test(..) -> []
      tao.Import(..) -> []
      _ -> [name]
    }
  })
}

/// Whether an entry is an `import` statement whose name is shadowed by a
/// local definition of the same module (see `shadowed_imports`).
fn shadowed_import(name: Name, stmt: Stmt, shadowed: List(Name)) -> Bool {
  case stmt.data {
    tao.Import(..) -> list.contains(shadowed, name)
    _ -> False
  }
}

/// Look up a definition by (module, name), lazily running phase 1 for
/// it if its module record does not exist yet. Callers must guard with
/// `has_def` so that an undefined *variable* is reported as an error
/// (`VarUndefined`) rather than hitting the panic below, which marks a
/// desugaring bug (the name was expected to be a module definition).
pub fn type_name(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
) -> #(v.Value, v.Type, Context) {
  step("type_name")
  case get_var(ctx, mod_name, name) {
    Some(#(val, typ)) -> #(val, typ, ctx)
    None ->
      case list.key_find(defs, mod_name) {
        Error(Nil) -> {
          echo list.map(defs, fn(entry) { entry.0 })
          echo mod_name
          panic as "error: module not found"
        }
        Ok(mod_defs) ->
          case list.key_find(mod_defs, name) {
            Error(Nil) -> {
              echo list.map(mod_defs, fn(entry) { entry.0 })
              echo #(mod_name, name)
              panic as "error: definition not found"
            }
            Ok(stmt) -> type_stmt(ctx, defs, mod_name, name, stmt)
          }
      }
  }
}

/// Whether `name` is a definition of `mod_name`: either already
/// registered in the context's module record, or pending in the
/// declaration table (so `type_name` can lazily register it).
fn has_def(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
) -> Bool {
  case get_var(ctx, mod_name, name) {
    Some(..) -> True
    None ->
      case list.key_find(defs, mod_name) {
        Error(Nil) -> False
        Ok(mod_defs) ->
          case list.key_find(mod_defs, name) {
            Ok(..) -> True
            Error(Nil) -> False
          }
      }
  }
}

/// `type_name` for a list of names in the same module.
pub fn type_name_list(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  names: List(Name),
) -> #(List(#(Name, v.Value)), List(#(Name, v.Type)), Context) {
  case names {
    [] -> #([], [], ctx)
    [name, ..names] -> {
      let #(val, typ, ctx) = type_name(ctx, defs, mod_name, name)
      let #(values, types, ctx) = type_name_list(ctx, defs, mod_name, names)
      #([#(name, val), ..values], [#(name, typ), ..types], ctx)
    }
  }
}

pub fn type_stmt(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  stmt: Stmt,
) -> #(v.Value, v.Type, Context) {
  // Reuse the existing entry when present. define.types processes every
  // entry of every module, and an import pre-creates the imported module's
  // entries (via type_name) before the module's own entries are processed.
  // Re-creating the holes here would overwrite the module's record with
  // fresh holes and orphan the copies already stored in the importing
  // module's record — holes that are never re-evaluated and can therefore
  // never be solved.
  case get_var(ctx, mod_name, name) {
    Some(#(val, typ)) -> #(val, typ, ctx)
    None -> {
      let #(val, typ, ctx) = type_stmt_data(ctx, defs, mod_name, name, stmt)
      let ctx = set_var(ctx, mod_name, name, val, typ)
      #(val, typ, ctx)
    }
  }
}

fn type_stmt_data(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  stmt: Stmt,
) -> #(v.Value, v.Type, Context) {
  let #(val, typ, ctx) = case stmt.data {
    tao.Import(path, alias, tao.ImportAll) -> {
      let names = case list.key_find(defs, path) {
        Ok(mod_defs) -> list.map(mod_defs, fn(entry) { #(entry.0, entry.0) })
        Error(Nil) -> {
          todo as "error: module not found"
        }
      }
      let stmt = tao.import_some(path, alias, names, stmt.span)
      type_stmt(ctx, defs, mod_name, name, stmt)
    }
    tao.Import(path, alias, tao.ImportSome(names)) ->
      case names {
        [] ->
          case list.key_find(defs, path) {
            Ok(mod_defs) -> {
              let names = list.map(mod_defs, fn(entry) { entry.0 })
              // The names belong to the imported module (path), not the
              // importing module (mod_name).
              let #(values, types, ctx) = type_name_list(ctx, defs, path, names)
              #(v.rcd(values), v.rcd(types), ctx)
            }
            Error(Nil) -> {
              echo list.map(defs, fn(entry) { entry.0 })
              echo path
              todo as "error: module not found"
            }
          }
        [#(x, y), ..] if name == y -> type_name(ctx, defs, path, x)
        [_, ..names] -> {
          let stmt = tao.import_some(path, alias, names, stmt.span)
          type_stmt(ctx, defs, mod_name, name, stmt)
        }
      }
    tao.Extern(name, ..) -> stmt_value(ctx, defs, mod_name, name, stmt, None)
    tao.LetVar(_, opt_type, _) -> {
      let #(val, ctx) = hole_value(ctx)
      let #(typ, ctx) = case opt_type {
        Some(tao_type) -> type_value(ctx, defs, mod_name, tao_type)
        None -> hole_value(ctx)
      }
      #(val, typ, ctx)
    }
    tao.LetPat(_pattern, _types, _value) -> todo
    tao.LetMut(_name, _opt_type, _value) -> todo
    tao.Mut(_name, _value) -> todo
    tao.Test(_name, _expr, _expect) -> {
      let #(val, ctx) = hole_value(ctx)
      let #(typ, ctx) = hole_value(ctx)
      #(val, typ, ctx)
    }
    tao.FnDef(name, ..) ->
      // TODO: Only derive the type annotation? Would this work for cyclic definitions?
      // If cyclic definitions still work like this, maybe separate define.types and define.values are not needed (could be simplified).
      stmt_value(ctx, defs, mod_name, name, stmt, None)
    tao.FnOverload(name, _) -> stmt_value(ctx, defs, mod_name, name, stmt, None)
    tao.TypeDef(..) -> {
      // A type definition is a value of the universe `Type`, and its
      // value can be computed directly in phase 1: the parameter types
      // are evaluated without inference, and constructor applications
      // inside the variants are tags (not references), so the
      // definition cannot refer to itself through the environment.
      // Storing the concrete value (instead of a hole) lets
      // `lookup_type_def` find the definition while the other bodies
      // are checked in phase 2.
      stmt_value(ctx, defs, mod_name, name, stmt, None)
    }
    tao.For(_iterator, _range, _body) -> todo
    tao.While(_condition, _body) -> todo
    tao.Return(_expr) -> todo
    tao.Break -> todo
    tao.Continue -> todo
  }
  #(val, typ, ctx)
}

/// Read one entry from a module record, if the module is in scope.
pub fn get_var(
  ctx: Context,
  mod_name: ModName,
  name: Name,
) -> Option(#(v.Value, v.Type)) {
  case context.lookup_var(ctx, mod_name) {
    Some(#(v.Rcd(mod_values, None), v.Rcd(mod_types, None))) -> {
      case list.key_find(mod_values, name), list.key_find(mod_types, name) {
        Ok(#(val, _)), Ok(#(typ, _)) -> Some(#(val, typ))
        _, _ -> None
      }
    }
    _ -> None
  }
}

/// Write one entry into a module record, creating the record if the
/// module is not in scope yet.
pub fn set_var(
  ctx: Context,
  mod_name: ModName,
  name: Name,
  val: v.Value,
  typ: v.Type,
) -> Context {
  let #(mod_val, mod_typ) = case context.lookup_var(ctx, mod_name) {
    Some(#(v.Rcd(values, None), v.Rcd(types, None))) -> #(
      v.Rcd(list_utils.set(values, name, #(val, None)), None),
      v.Rcd(list_utils.set(types, name, #(typ, None)), None),
    )
    _ -> #(v.rcd([#(name, val)]), v.rcd([#(name, typ)]))
  }
  context.set_var(ctx, mod_name, mod_val, mod_typ)
}

/// Not implemented: list a module's entries with optional value/type.
pub fn get_mod_vars(
  _ctx: Context,
  _mod_name: ModName,
) -> List(#(Name, Option(v.Value), Option(v.Type))) {
  todo
}

fn hole_value(ctx: Context) -> #(v.Value, Context) {
  let #(id, ctx) = context.new_hole(ctx)
  #(v.hole(ctx.env, id), ctx)
}

fn expr_value(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  expr: tao.Expr,
  opt_type: Option(v.Type),
) -> #(v.Value, v.Type, Context) {
  step("expr_value")
  let exports = declare.exports(defs)
  let core_expr = desugar.expr(exports, expr)
  // Free variables that are not module names (names start with "/") are
  // local definitions of the current module; each one is brought into
  // scope by lazily registering it (which may create fresh holes).
  let deps =
    core.free_vars(core_expr)
    |> list.filter(fn(name) { !string.starts_with(name, "/") })
  let ctx =
    list.fold(deps, ctx, fn(ctx, name) {
      // A free local name must be a definition of the current module (or
      // an import expanded into it). Anything else is an undefined
      // variable: report it and bind `Err` so checking can continue and
      // the rest of the definition still produces useful errors.
      case has_def(ctx, defs, mod_name, name) {
        True -> {
          let #(val, typ, ctx) = type_name(ctx, defs, mod_name, name)
          context.push_var(ctx, #(name, val, typ))
        }
        False -> {
          let ctx = context.with_err(ctx, e.VarUndefined(name), expr.span)
          context.push_var(ctx, #(name, v.Err, v.Err))
        }
      }
    })
  let #(term, typ, ctx) = case opt_type {
    Some(typ) -> check(ctx, core_expr, #(typ, expr.span))
    None -> infer(ctx, core_expr)
  }
  let value = eval(ctx.ffi, ctx.env, term)
  let ctx = context.pop_vars(ctx, list.length(deps))
  #(value, typ, ctx)
}

fn type_value(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  typ: tao.Type,
) -> #(v.Type, Context) {
  let #(core_type, _, ctx) = expr_value(ctx, defs, mod_name, typ, None)
  #(core_type, ctx)
}

/// Infer a statement as the body of a block that returns the bound
/// name, so the statement's value is the name's value in scope.
pub fn stmt_value(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  stmt: tao.Stmt,
  opt_type: Option(v.Type),
) -> #(v.Value, v.Type, Context) {
  // Overload dispatch is a blind runtime match on the arguments'
  // constructor types (the evaluator does no type lookups), so the
  // type names in an overloaded function's choices are expanded into
  // concrete constructor patterns first (see docs/overloads.md).
  case stmt.data {
    tao.FnOverload(fn_name, choices) -> {
      let #(choices, ctx) = expand_overload_choices(ctx, choices)
      let stmt = tao.Stmt(tao.FnOverload(fn_name, choices), stmt.span)
      stmt_value_inner(ctx, defs, mod_name, name, stmt, opt_type)
    }
    _ -> stmt_value_inner(ctx, defs, mod_name, name, stmt, opt_type)
  }
}

fn stmt_value_inner(
  ctx: Context,
  defs: List(#(ModName, List(#(Name, Stmt)))),
  mod_name: ModName,
  name: Name,
  stmt: tao.Stmt,
  opt_type: Option(v.Type),
) -> #(v.Value, v.Type, Context) {
  let s = stmt.span
  let tao_expr = tao.do([stmt, tao.return(tao.var(name, s), s)], s)
  expr_value(ctx, defs, mod_name, tao_expr, opt_type)
}

/// Expand the type names in an overloaded function's choice patterns
/// into concrete constructor patterns, so the dispatch match — a blind
/// runtime match on the arguments' types — selects the right choice
/// (see docs/overloads.md).
///
/// A value's type is its constructor application: a value of type `Bool`
/// has the *variant's* constructor application as its type (`#True{}` or
/// `#False{}`), or the type constructor itself (`#Bool{}`) when only the
/// declared type is known. Core patterns have no disjunction, so each
/// choice is replicated for the product of its argument patterns'
/// alternatives. Arguments that do not name a type definition are left
/// unchanged: `unify`'s Ctr-vs-Typ rule reports them as type errors.
pub fn expand_overload_choices(
  ctx: Context,
  choices: List(tao.OverloadChoice),
) -> #(List(tao.OverloadChoice), Context) {
  list.fold(choices, #([], ctx), fn(acc, choice) {
    let #(expanded, ctx) = expand_choice(ctx, choice)
    #(list.append(acc.0, expanded), ctx)
  })
}

/// One choice with its argument patterns expanded: the product of the
/// alternatives of each argument pattern, one choice per combination
/// (same module, name, guard and span as the original).
fn expand_choice(
  ctx: Context,
  choice: tao.OverloadChoice,
) -> #(List(tao.OverloadChoice), Context) {
  let names = list.map(choice.args, fn(arg) { arg.0 })
  let #(alternatives, ctx) =
    list.fold(choice.args, #([], ctx), fn(acc, arg) {
      let #(_, pat) = arg
      let #(alts, ctx) = pattern_alternatives(ctx, pat)
      #([alts, ..acc.0], ctx)
    })
  let combos = product(list.reverse(alternatives))
  let expanded =
    list.map(combos, fn(pats) {
      let args = list.zip(names, pats)
      tao.OverloadChoice(choice.mod_name, choice.name, args, choice.guard, choice.span)
    })
  #(expanded, ctx)
}

/// The concrete constructor patterns one choice argument pattern
/// matches: a type name (`Bool`, `Option(Int)`) expands to itself (the
/// type constructor application, as written) plus one pattern per
/// variant (constructor tag with any arguments, since a value of type
/// `Bool` has type `#True{}` or `#False{}`); any other pattern (literal
/// types, variables, wildcards) is its own single alternative.
fn pattern_alternatives(
  ctx: Context,
  pat: tao.Pattern,
) -> #(List(tao.Pattern), Context) {
  case pat.data {
    tao.PCtr(tag, _, _) ->
      case lookup_type_def(ctx, tag) {
        Some(#(_, tdef)) -> {
          let variants =
            list.map(tdef.variants, fn(variant) {
              let #(variant_tag, _) = variant
              tao.pctr_open(variant_tag, [], Some(tao.pany(pat.span)), pat.span)
            })
          #([pat, ..variants], ctx)
        }
        None -> #([pat], ctx)
      }
    _ -> #([pat], ctx)
  }
}

/// The product of a list of alternative lists: one list per combination
/// (in the order of the alternatives).
fn product(alternatives: List(List(a))) -> List(List(a)) {
  case alternatives {
    [] -> [[]]
    [first, ..rest] -> {
      let rest_combos = product(rest)
      list.flat_map(first, fn(item) {
        list.map(rest_combos, fn(combo) { [item, ..combo] })
      })
    }
  }
}
