/// Substitution - Hole resolution and level-to-index conversion.
///
/// The `subst` module handles two key operations in the compiler pipeline:
///
/// 1. **`force`** - Resolves holes (unbound metavariables) by looking them
///    up in the state, then applies the resulting neutral spine through beta
///    reduction. This turns a potentially open neutral term into a value.
///
/// 2. **`force_levels_to_indices`** - Converts a `Value` (which uses De Bruijn
///    levels for variables) into a `Term` (which uses De Bruijn indices).
///    This is used by the quote module to turn runtime values back into
///    syntax.
///
/// ## How `force` works
///
/// ```
/// // A hole in a neutral term is resolved by looking up its binding in state
/// force(state, VNeut(HHole(id), []))
///   -> force(state, resolved_value)
///
/// // A lambda application consumes one spine element via beta reduction
/// force(state, VNeut(HHole(id), [EApp(arg)]))
///   -> body with arg bound at level 0
/// ```
import core/ast.{
  type Term, type Value, type Elim, type Head,
  Ann, App, Call, Case, Ctr, EApp, Err, HHole, HVar, Hole, Lam, Lit, Match, Pi, Rcd, RcdT, Typ, VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, VRcdT, VTyp, VTypeDef, TypeDef, Var, LitT, VLitT,
  make_neut, shift_opt, shift_term, value_to_string, term_to_string,
}
import core/state.{type State, lookup_var}
import syntax/span.{type Span, single}
import gleam/int
import gleam/list
import gleam/option.{None, Some}

/// Force a value by resolving holes and applying neutral spine elements.
///
/// This function performs two operations:
///
/// 1. **Hole resolution** - If the value's head is a hole (`HHole(id)`), look
///    up the binding in state (`"hole{id}"`) and substitute it.
///
/// 2. **Spine application** - Apply each `EApp(arg)` in the spine by doing
///    beta reduction if the head is a lambda, or building a new neutral term
///    if not.
///
/// Holes without bindings are reported as errors and replaced with `VErr`.
pub fn force(state: State, value: Value) -> Value {
  case value {
    VNeut(head, spine) -> {
      let resolved = resolve_head(state, head)
      case resolved {
        Ok(v) -> apply_spine(v, spine)
        Error(_) -> value
      }
    }
    _ -> value
  }
}

/// Resolve a neutral head to a value by looking it up in state.
fn resolve_head(state: State, head: Head) -> Result(Value, Nil) {
  case head {
    HHole(id) -> {
      let binding_name = "hole" <> int.to_string(id)
      case lookup_var(state, binding_name) {
        Ok(#(value, _type)) -> Ok(value)
        Error(_) -> Error(Nil)
      }
    }
    HVar(level) -> {
      case lookup_level_local(state.vars, level) {
        Ok(#(value, _type)) -> Ok(value)
        Error(_) -> Error(Nil)
      }
    }
  }
}

/// Look up a variable by De Bruijn level from the outermost binding.
fn lookup_level_local(
  vars: List(#(String, #(Value, Value))),
  level: Int,
) -> Result(#(Value, Value), Nil) {
  case vars, level {
    [#(_, val), ..], 0 -> Ok(val)
    [_, ..rest], _ -> lookup_level_local(rest, level - 1)
    [], _ -> Error(Nil)
  }
}

/// Look up a variable by De Bruijn level from the outermost binding.
/// Apply a list of eliminators (a neutral spine) to a value.
pub fn apply_spine(value: Value, spine: List(Elim)) -> Value {
  case spine {
    [] -> value
    [elim, ..rest] -> {
      let forced_arg = elim_arg_value(elim)
      case try_apply(value, forced_arg) {
        Ok(new_val) -> apply_spine(new_val, rest)
        Error(_) -> make_neut(HVar(0))
      }
    }
  }
}

/// Extract the value from an eliminator.
fn elim_arg_value(elim: Elim) -> Value {
  case elim {
    EApp(arg) -> arg
  }
}

/// Attempt to apply `arg` to `value`.
/// Returns `Ok(result)` if beta reduction succeeds, `Error(Nil)` otherwise.
fn try_apply(value: Value, arg: Value) -> Result(Value, Nil) {
  case value {
    VLam(env, implicits, param, body) -> {
      let shifted_body = shift_term(body, 1)
      let substituted = subst_term_var(0, arg, shifted_body)
      // Return the substituted term wrapped in a lambda - evaluation
      // happens when this lambda is applied
      Ok(VLam(env, implicits, param, substituted))
    }
    _ -> Error(Nil)
  }
}

/// Substitute variable at index `idx` with `value` in a shifted term body.
pub fn subst_term_var(idx: Int, value: Value, term: Term) -> Term {
  subst_term_from(idx, value, term, 0)
}

fn subst_term_from(idx: Int, value: Value, term: Term, from: Int) -> Term {
  case term {
    Var(i, span) ->
      // Substitute Var(idx + from) which corresponds to the variable at
      // the outer scope's index `idx`. The `from` parameter tracks nesting
      // depth - inside a lambda, Var(0) refers to the lambda's parameter,
      // while Var(1) refers to the outer scope's Var(0), etc.
      case i == idx + from {
        True -> value_to_neut(value)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(implicits, #(name, param), body, span) ->
      Lam(
        list.map(implicits, fn(i) { #(i.0, subst_term_from(idx, value, i.1, from)) }),
        #(name, subst_term_from(idx, value, param, from)),
        subst_term_from(idx, value, body, from + 1 + list.length(implicits)),
        span,
      )
    App(fun, arg, span) ->
      App(
        subst_term_from(idx, value, fun, from),
        subst_term_from(idx, value, arg, from),
        span,
      )
    Pi(implicits, #(name, domain), codomain, span) ->
      Pi(
        list.map(implicits, fn(i) { #(i.0, subst_term_from(idx, value, i.1, from)) }),
        #(name, subst_term_from(idx, value, domain, from)),
        subst_term_from(idx, value, codomain, from + 1 + list.length(implicits)),
        span,
      )
    Lit(lit, span) -> Lit(lit, span)
    Ctr(tag, arg, span) ->
      Ctr(tag, subst_term_from(idx, value, arg, from), span)
    Match(arg, cases, span) ->
      Match(
        subst_term_from(idx, value, arg, from),
        list.map(cases, fn(c) {
          Case(
            c.pattern,
            shift_opt(c.guard, from, from),
            subst_term_from(idx, value, c.body, from),
            c.span,
          )
        }),
        span,
      )
    Ann(t, type_, span) ->
      Ann(
        subst_term_from(idx, value, t, from),
        subst_term_from(idx, value, type_, from),
        span,
      )
    Call(name, args, typed_args, return_type, span) ->
      Call(
        name,
        list.map(args, fn(a) { subst_term_from(idx, value, a, from) }),
        list.map(typed_args, fn(ta) { #(subst_term_from(idx, value, ta.0, from), subst_term_from(idx, value, ta.1, from)) }),
        case return_type {
          Some(t) -> Some(subst_term_from(idx, value, t, from))
          None -> None
        },
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(f) {
          #(f.0, subst_term_from(idx, value, f.1, from))
        }),
        span,
      )
    RcdT(fields, span) ->
      RcdT(
        list.map(fields, fn(f) {
          #(f.0, subst_term_from(idx, value, f.1, from), case f.2 {
            Some(t) -> Some(subst_term_from(idx, value, t, from))
            None -> None
          })
        }),
        span,
      )
    Typ(level, span) -> Typ(level, span)
    LitT(ltype, span) -> LitT(ltype, span)
    TypeDef(name: name, params: params, constructors: cons, span: span) -> {
      let shift_cons = fn(ctor) {
        case ctor {
          #(tag, bindings, self_ty, result, c_span) -> {
            let new_self = subst_term_from(idx, value, self_ty, from)
            let new_result = subst_term_from(idx, value, result, from)
            #(tag, bindings, new_self, new_result, c_span)
          }
        }
      }
      TypeDef(
        name: name,
        params: params,
        constructors: list.map(cons, shift_cons),
        span: span,
      )
    }
    Err(msg, span) -> Err(msg, span)
  }
}

/// Convert a Value to a Term.
///
/// For neutral values, extracts the head and returns a neutral term.
/// For other values (literals, constructors, records), converts
/// De Bruijn levels to De Bruijn indices.
fn value_to_neut(value: Value) -> Term {
  case value {
    VNeut(head, []) -> neut_head_to_term(head)
    _ -> force_levels_to_indices(value, 0)
  }
}

fn neut_head_to_term(head: Head) -> Term {
  case head {
    HVar(level) -> Var(level, single("", 0, 0))
    HHole(id) -> Hole(id, single("", 0, 0))
  }
}

// ============================================================================
// LEVEL → INDEX CONVERSION (Value → Term)
// ============================================================================

/// Convert a `Value` to a `Term` by converting De Bruijn levels to indices.
///
/// This is the core operation of the quote module. It walks through a value
/// and converts every De Bruijn level reference to the equivalent De Bruijn
/// index:
///
/// - `HVar(l)` where `l < n` → `Var(n - 1 - l, span)` (bound variable)
/// - `HVar(l)` where `l >= n` → `Var(l - n, span)` (free variable)
/// - `HHole(id)` → `Hole(id, span)`
///
/// ## Parameters
///
/// `n` is the number of binders between the value's scope and the term's
/// scope. For the top-level value (e.g., the result of evaluating a program),
/// use `n = 0`.
pub fn force_levels_to_indices(value: Value, n: Int) -> Term {
  case value {
    VNeut(head, spine) -> neut_head_to_term_with_spine(head, spine, n)
    VLam(_env, implicits, param, body) -> {
      // VLam's body is already a Term - convert param type (Value) to Term
      let new_n = n + 1
      let converted_implicits = list.map(implicits, fn(i) { #(i.0, force_levels_to_indices(i.1, new_n)) })
      let converted_param = #(param.0, force_levels_to_indices(param.1, new_n))
      Lam(converted_implicits, converted_param, body, single("", 0, 0))
    }
    VPi(_env, implicits, domain, codomain) -> {
      let new_n = n + 1
      let converted_implicits = list.map(implicits, fn(i) { #(i.0, force_levels_to_indices(i.1, new_n)) })
      let converted_domain = #(domain.0, force_levels_to_indices(domain.1, new_n))
      let converted_codomain = force_levels_to_indices(codomain, new_n)
      Pi(converted_implicits, converted_domain, converted_codomain, single("", 0, 0))
    }
    VLit(lit) -> Lit(lit, single("", 0, 0))
    VCtr(tag, arg) ->
      Ctr(tag, force_levels_to_indices(arg, n), single("", 0, 0))
    VRcd(fields) ->
      Rcd(
        list.map(fields, fn(f) { #(f.0, force_levels_to_indices(f.1, n)) }),
        single("", 0, 0),
      )
    VRcdT(fields) ->
      RcdT(
        list.map(fields, fn(f) {
          let default_term = case f.2 {
            Some(d) -> Some(force_levels_to_indices(d, n))
            None -> None
          }
          #(f.0, force_levels_to_indices(f.1, n), default_term)
        }),
        single("", 0, 0),
      )
    VTypeDef(name: vname, params: vparams, constructors: c) -> {
      let params_terms = list.map(vparams, fn(p) {
        #(p.0, force_levels_to_indices(p.1, n))
      })
      let shift_cons = fn(ctor: #(String, List(String), Value, Value, Span)) -> #(String, List(String), Term, Term, Span) {
        let a = case ctor { #(x, _, _, _, _) -> x }
        let bindings = case ctor { #(_, x, _, _, _) -> x }
        let b = case ctor { #(_, _, x, _, _) -> x }
        let result = case ctor { #(_, _, _, x, _) -> x }
        let d = case ctor { #(_, _, _, _, x) -> x }
        let r1: Term = force_levels_to_indices(b, n)
        let r2: Term = force_levels_to_indices(result, n)
        let r3: #(String, List(String), Term, Term, Span) = #(a, bindings, r1, r2, d)
        r3
      }
      let typed_constructors: List(#(String, List(String), Term, Term, Span)) = list.map(c, shift_cons)
      TypeDef(
        name: vname,
        params: params_terms,
        constructors: typed_constructors,
        span: single("", 0, 0),
      )
    }
    VErr -> Err("error", single("", 0, 0))
    VTyp(level) -> Typ(level, single("", 0, 0))
    VLitT(ltype) -> LitT(ltype, single("", 0, 0))
  }
}

/// Convert a neutral head and its spine to a term.
fn neut_head_to_term_with_spine(head: Head, spine: List(Elim), n: Int) -> Term {
  case head, spine {
    HVar(level), [] -> Var(abs_index(level, n), single("", 0, 0))
    HHole(id), [] -> Hole(id, single("", 0, 0))
    HVar(level), [EApp(arg), ..rest] -> {
      let base = Var(abs_index(level, n), single("", 0, 0))
      let arg_term = force_levels_to_indices(arg, n)
      let applied = App(base, arg_term, single("", 0, 0))
      apply_remaining_spine(applied, n, rest)
    }
    HHole(id), [EApp(arg), ..rest] -> {
      let base = Hole(id, single("", 0, 0))
      let arg_term = force_levels_to_indices(arg, n)
      let applied = App(base, arg_term, single("", 0, 0))
      apply_remaining_spine(applied, n, rest)
    }
  }
}

/// Continue applying remaining spine elements to a term.
fn apply_remaining_spine(base: Term, n: Int, rest: List(Elim)) -> Term {
  case rest {
    [] -> base
    [EApp(next_arg), ..rest_rest] -> {
      let next_term = force_levels_to_indices(next_arg, n)
      let applied = App(base, next_term, single("", 0, 0))
      apply_remaining_spine(applied, n, rest_rest)
    }
  }
}

/// Calculate the De Bruijn index from a De Bruijn level.
fn abs_index(level: Int, n: Int) -> Int {
  case level < n {
    True -> n - 1 - level
    False -> level - n
  }
}

// ============================================================================
// STRING REPRESENTATION (Debug)
// ============================================================================

/// Format a force result as a human-readable string for debugging.
pub fn force_to_string(value: Value) -> String {
  value_to_string(value)
}

/// Convert a value's level-to-index conversion result to a string.
pub fn levels_to_indices_to_string(term: Term) -> String {
  term_to_string(term)
}
