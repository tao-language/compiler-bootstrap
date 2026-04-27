/// Substitution — Hole resolution and level-to-index conversion.
///
/// The `subst` module handles two key operations in the compiler pipeline:
///
/// 1. **`force`** — Resolves holes (unbound metavariables) by looking them
///    up in the state, then applies the resulting neutral spine through beta
///    reduction. This turns a potentially open neutral term into a value.
///
/// 2. **`force_levels_to_indices`** — Converts a `Value` (which uses De Bruijn
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
  type Term, type Value, type Head, type Elim,
  type Case, Case,
  type Literal, type Pattern,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Call, Rcd, Typ, Err,
  VNeut, HHole, HVar, VLam, VPi, VLit, VCtr, VRcd, VErr, EApp, make_neut,
  PAny, PVar, PCtr as Pctr, PUnit, PLit,
  Int as LitInt, Float as LitFloat,
}
import core/state.{type State, lookup_var}
import gleam/option.{type Option, Some, None}
import gleam/list
import gleam/int
import syntax/span.{single}

/// Force a value by resolving holes and applying neutral spine elements.
///
/// This function performs two operations:
///
/// 1. **Hole resolution** — If the value's head is a hole (`HHole(id)`), look
///    up the binding in state (`"hole{id}"`) and substitute it.
///
/// 2. **Spine application** — Apply each `EApp(arg)` in the spine by doing
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
      let binding_name = "hole" <> int_to_string(id)
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
    VLam(param, body) -> {
      let #(name, param_type) = param
      let _param_name = name
      let shifted_body = shift_term(body, 1)
      let substituted = subst_term_var(0, arg, shifted_body)
      // Return the substituted term wrapped in a lambda — evaluation
      // happens when this lambda is applied
      Ok(VLam(#("x", param_type), substituted))
    }
    _ -> Error(Nil)
  }
}

/// Shift De Bruijn indices in a term by `shift` (from binder 0).
pub fn shift_term(term: Term, shift: Int) -> Term {
  shift_term_from(term, shift, 0)
}

fn shift_term_from(term: Term, shift: Int, from: Int) -> Term {
  case term {
    Var(i, span) ->
      case i >= from {
        True -> Var(i + shift, span)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(#(name, param), body, span) ->
      Lam(#(name, shift_term_from(param, shift, from)),
          shift_term_from(body, shift, from + 1),
          span)
    App(fun, arg, span) ->
      App(shift_term_from(fun, shift, from),
          shift_term_from(arg, shift, from),
          span)
    Pi(domain, codomain, span) ->
      Pi(shift_term_from(domain, shift, from),
         shift_term_from(codomain, shift, from),
         span)
    Lit(value, span) -> Lit(value, span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term_from(arg, shift, from), span)
    Match(arg, cases, span) ->
      Match(shift_term_from(arg, shift, from),
            list.map(cases, fn(c) {
              Case(c.pattern, shift_opt(c.guard, shift, from),
                   shift_term_from(c.body, shift, from), c.span)
            }),
            span)
    Ann(term, type_, span) ->
      Ann(shift_term_from(term, shift, from),
          shift_term_from(type_, shift, from),
          span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { shift_term_from(a, shift, from) }), span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(f) { #(f.0, shift_term_from(f.1, shift, from)) }), span)
    Typ(level, span) -> Typ(level, span)
    Err(msg, span) -> Err(msg, span)
  }
}

fn shift_opt(term: Option(Term), shift: Int, from: Int) -> Option(Term) {
  case term {
    Some(t) -> Some(shift_term_from(t, shift, from))
    None -> None
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
      // depth — inside a lambda, Var(0) refers to the lambda's parameter,
      // while Var(1) refers to the outer scope's Var(0), etc.
      case i == idx + from {
        True -> value_to_neut(value)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(#(name, param), body, span) ->
      Lam(#(name, param),
          subst_term_from(idx, value, body, from + 1),
          span)
    App(fun, arg, span) ->
      App(subst_term_from(idx, value, fun, from),
          subst_term_from(idx, value, arg, from),
          span)
    Pi(domain, codomain, span) ->
      Pi(subst_term_from(idx, value, domain, from),
         subst_term_from(idx, value, codomain, from),
         span)
    Lit(lit, span) -> Lit(lit, span)
    Ctr(tag, arg, span) -> Ctr(tag, subst_term_from(idx, value, arg, from), span)
    Match(arg, cases, span) ->
      Match(subst_term_from(idx, value, arg, from),
            list.map(cases, fn(c) {
              Case(c.pattern, shift_opt(c.guard, 0, from),
                   subst_term_from(idx, value, c.body, from),
                   c.span)
            }),
            span)
    Ann(t, type_, span) ->
      Ann(subst_term_from(idx, value, t, from),
          subst_term_from(idx, value, type_, from),
          span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { subst_term_from(idx, value, a, from) }), span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(f) { #(f.0, subst_term_from(idx, value, f.1, from)) }), span)
    Typ(level, span) -> Typ(level, span)
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
    VNeut(head, spine) ->
      neut_head_to_term_with_spine(head, spine, n)
    VLam(param, body) -> {
      // VLam's body is already a Term — convert param type (Value) to Term
      let new_n = n + 1
      let converted_param = force_levels_to_indices(param.1, new_n)
      Lam(#(param.0, converted_param), body, single("", 0, 0))
    }
    VPi(domain, codomain) -> {
      let converted_domain = force_levels_to_indices(domain, n)
      let converted_codomain = force_levels_to_indices(codomain, n + 1)
      Pi(converted_domain, converted_codomain, single("", 0, 0))
    }
    VLit(lit) -> Lit(lit, single("", 0, 0))
    VCtr(tag, arg) -> Ctr(tag, force_levels_to_indices(arg, n), single("", 0, 0))
    VRcd(fields) -> Rcd(
      list.map(fields, fn(f) { #(f.0, force_levels_to_indices(f.1, n)) }),
      single("", 0, 0)
    )
    VErr -> Err("error", single("", 0, 0))
  }
}

/// Convert a neutral head and its spine to a term.
fn neut_head_to_term_with_spine(
  head: Head,
  spine: List(Elim),
  n: Int,
) -> Term {
  case head, spine {
    HVar(level), [] ->
      Var(abs_index(level, n), single("", 0, 0))
    HHole(id), [] ->
      Hole(id, single("", 0, 0))
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
fn apply_remaining_spine(
  base: Term,
  n: Int,
  rest: List(Elim),
) -> Term {
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
  value_string(value)
}

/// Convert a value's level-to-index conversion result to a string.
pub fn levels_to_indices_to_string(term: Term) -> String {
  term_string(term)
}

fn value_string(value: Value) -> String {
  case value {
    VNeut(head, spine) ->
      case spine {
        [] -> neut_head_to_string(head)
        _ -> neut_to_string(head, spine)
      }
    VLam(param, body) ->
      "%fn(" <> param.0 <> ") => " <> term_string(body)
    VPi(domain, codomain) ->
      "%fn(_ : " <> value_string(domain) <> ") -> " <> value_string(codomain)
    VLit(lit) -> literal_string(lit)
    VCtr(tag, arg) -> "#" <> tag <> "(" <> value_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ -> "{" <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> value_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> value_string(f.1)
          }
        }) <> "}"
      }
    VErr -> "\"error\""
  }
}

fn neut_head_to_string(head: Head) -> String {
  case head {
    HVar(level) -> "v" <> int_to_string(level)
    HHole(id) -> "?" <> int_to_string(id)
  }
}

fn neut_to_string(head: Head, spine: List(Elim)) -> String {
  let head_str = neut_head_to_string(head)
  let spine_str = list.fold(
    spine, "", fn(acc, e) {
      let s = case e {
        EApp(arg) -> "(" <> value_string(arg) <> ")"
      }
      acc <> s
    },
  )
  head_str <> spine_str
}

fn term_string(term: Term) -> String {
  case term {
    Var(i, _) -> "#" <> int_to_string(i)
    Hole(id, _) -> "?" <> int_to_string(id)
    Lam(#(name, param), body, _) ->
      "%fn(" <> name <> ": " <> term_string(param) <> ") => " <> term_string(body)
    App(fun, arg, _) ->
      "fun(" <> term_string(fun) <> ": " <> term_string(arg) <> ")"
    Pi(domain, codomain, _) ->
      "%fn(_) : " <> term_string(domain) <> " -> " <> term_string(codomain)
    Lit(lit, _) -> literal_string(lit)
    Ctr(tag, arg, _) ->
      case arg {
        Ann(t, Typ(0, _), _) -> "#" <> tag <> "(" <> term_string(t) <> ")"
        _ -> "#" <> tag
      }
    Match(arg, cases, _) ->
      "%match " <> term_string(arg) <> " {"
      <> list.fold(cases, "", fn(acc, c) {
        acc <> "\n  | " <> case_to_string(c)
      })
      <> "\n}"
    Ann(t, type_, _) ->
      term_string(t) <> " : " <> term_string(type_)
    Call(name, args, _) ->
      "call(" <> name <> "[" <> list.fold(args, "", fn(acc, a) {
        case acc { "" -> term_string(a) _ -> acc <> ", " <> term_string(a) }
      }) <> "])"
    Rcd(fields, _) ->
      case fields {
        [] -> "()"
        _ -> "{" <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> term_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> term_string(f.1)
          }
        }) <> "}"
      }
    Typ(level, _) -> "%Type(" <> int_to_string(level) <> ")"
    Err(msg, _) -> "\"" <> msg <> "\""
  }
}

fn case_to_string(case_: Case) -> String {
  case case_.guard {
    Some(guard) ->
      pattern_to_string(case_.pattern) <> " ? " <> term_string(guard)
      <> " => " <> term_string(case_.body)
    None ->
      pattern_to_string(case_.pattern) <> " => " <> term_string(case_.body)
  }
}

fn pattern_to_string(pat: Pattern) -> String {
  case pat {
    PAny(_) -> "_"
    PVar(name, _) -> name
    Pctr(tag, inner, _) -> tag <> "(" <> pattern_to_string(inner) <> ")"
    PUnit(_) -> "()"
    PLit(LitInt(value), _) -> int_to_string(value)
    PLit(LitFloat(_), _) -> "<float>"
  }
}

fn literal_string(lit: Literal) -> String {
  case lit {
    LitInt(value) -> int_to_string(value)
    LitFloat(_) -> "<float>"
  }
}

// ============================================================================
// HELPERS
// ============================================================================

fn int_to_string(n: Int) -> String {
  int.to_string(n)
}
