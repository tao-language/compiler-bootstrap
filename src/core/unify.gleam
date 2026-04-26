/// Unification — Higher-order unification for Core values.
///
/// Unification checks whether two `Value`s are "the same" and records
/// any mismatches as errors in the `State`. It also resolves holes
/// (unbound metavariables) by binding them to their types.
///
/// ## How it works
///
/// `unify(state, expected, actual)` recursively compares the two values:
///
/// - **Holes** (`VNeut(HHole(id))`) — unbound metavariables. When the
///   expected type is a hole, we bind it to the actual type in state.
/// - **Variables** (`VNeut(HVar(level))`) — look up the binding in state.
/// - **Same constructors** — recursively unify their fields.
/// - **Mismatched constructors** — record a `TypeMismatch` error.
///
/// The type checker calls this function at every place where two types
/// must agree. All errors accumulate in state; no early returns.

import core/ast.{
  type Value,
  type Term,
  type Case,
  type Pattern,
  type Head,
  type Elim,
  VNeut, HHole, HVar, VLam, VPi, VCtr, VLit, VRcd, VErr, EApp,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Rcd, Typ, Err, Call,
  Case,
  PAny, PVar, PCtr, PUnit, PLit,
}
import core/state.{type State, State, with_err, TypeMismatch}
import gleam/list
import gleam/int
import gleam/string
import gleam/option.{type Option, Some, None}
import syntax/span.{type Span, single}

/// Unify two values: `expected` is the type being checked against,
/// `actual` is the value whose type must match.
///
/// Returns the state (with errors accumulated if the types differ).
///
/// ## Example
///
/// ```gleam
/// import core/unify.{unify}
/// import core/state.{initial_state}
/// import core/ast.{VLit, VNeut, HHole, LitInt}
///
/// let state = initial_state([])
/// // A hole unifies with any concrete value — binds the hole
/// let final = unify(state, VNeut(HHole(0), []), VLit(LitInt(42)))
/// ```
pub fn unify(state: State, expected: Value, actual: Value) -> State {
  match_values(state, expected, actual)
}

// ── Core matching logic ───────────────────────────────────────────

fn match_values(state: State, expected: Value, actual: Value) -> State {
  case expected, actual {
    // ── Same variable level — trivially unified ──────────────
    VNeut(HVar(l1), _), VNeut(HVar(l2), _) if l1 == l2 -> state

    // ── Variable in expected — look up in state ──────────────
    VNeut(HVar(level), _), _ -> {
      case lookup_level(state, level) {
        Ok(#(value, _)) -> match_values(state, value, actual)
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }
    }

    // ── Same variable level in actual — look up in state ────
    _, VNeut(HVar(l1), _) if l1 >= 0 ->
      case lookup_level(state, l1) {
        Ok(#(value, _)) -> match_values(state, expected, value)
        Error(_) -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Different holes — mismatch ───────────────────────────
    VNeut(HHole(id1), []), VNeut(HHole(id2), _) if id1 != id2 ->
      add_type_mismatch_error(state, expected, actual)

    // ── Hole in expected — bind it ───────────────────────────
    VNeut(HHole(id), []), _ -> bind_hole(state, id, actual)

    // ── Same hole ID — trivially unified ─────────────────────
    VNeut(HHole(id1), _), VNeut(HHole(id2), _) if id1 == id2 -> state

    // ── Hole in actual — bind it ─────────────────────────────
    _, VNeut(HHole(id), []) -> bind_hole(state, id, expected)

    // ── Neutral — neutral comparison ─────────────────────────
    VNeut(head1, spine1), VNeut(head2, spine2) ->
      match_neutral(state, head1, spine1, head2, spine2)

    // ── Lambda — unify param types, then bodies under binding ─
    VLam(#(_, ptype1), body1), VLam(#(_, ptype2), body2) -> {
      let s1 = match_values(state, ptype1, ptype2)
      // Unify bodies as terms (both are Lambda bodies after beta reduction)
      let s2 = unify_terms(s1, body1, shift_term(body2, 1))
      s2
    }

    // ── Pi types — unify domains, then codomains ─────────────
    VPi(domain1, codomain1), VPi(domain2, codomain2) -> {
      let s1 = match_values(state, domain1, domain2)
      let bound = State(..s1, vars: [#("pi_param", #(domain2, domain2)), ..s1.vars])
      match_values(bound, codomain1, shift_value(codomain2, 1))
    }

    // ── Constructor — tag must match, then unify args ────────
    VCtr(tag1, arg1), VCtr(tag2, arg2) ->
      case tag1 == tag2 {
        True -> match_values(state, arg1, arg2)
        False -> add_type_mismatch_error(
          state,
          VCtr(tag1, VNeut(HHole(0), [])),
          VCtr(tag2, VNeut(HHole(0), [])),
        )
      }

    // ── Literal — value must be equal ────────────────────────
    VLit(lit1), VLit(lit2) ->
      case lit1 == lit2 {
        True -> state
        False -> add_type_mismatch_error(state, expected, actual)
      }

    // ── Record — unify field by field ────────────────────────
    VRcd(fields1), VRcd(fields2) ->
      match_records(state, fields1, fields2)

    // ── VErr — unifies with any value (error recovery) ───────
    VErr, _ -> state
    _, VErr -> state

    // ── Anything else — type mismatch ────────────────────────
    _, _ -> add_type_mismatch_error(state, expected, actual)
  }
}

// ── Hole binding ──────────────────────────────────────────────────

/// Bind a hole to a value.
///
/// Stores the binding in the variable environment using the name
/// `"hole{id}"` for lookup later.
fn bind_hole(state: State, id: Int, value: Value) -> State {
  // Occurs check: skip binding if it would create a cycle
  case occurs_check(id, value) {
    True -> state
    False -> {
      // Check if this hole already has a binding
      case find_hole_binding(state, id) {
        Ok(already_bound) -> match_values(state, already_bound, value)
        Error(Nil) -> {
          let binding_name = "hole" <> int.to_string(id)
          State(..state, vars: [#(binding_name, #(value, value)), ..state.vars])
        }
      }
    }
  }
}

// ── Variable lookup ───────────────────────────────────────────────

/// Look up a De Bruijn level in the state's variable bindings.
fn lookup_level(state: State, level: Int) -> Result(#(Value, Value), Nil) {
  case list.drop(state.vars, level) {
    [#(_, #(value, type_)), ..] -> Ok(#(value, type_))
    _ -> Error(Nil)
  }
}

/// Find a hole binding by ID.
fn find_hole_binding(state: State, id: Int) -> Result(Value, Nil) {
  let prefix = "hole" <> int.to_string(id)
  find_hole_loop(state.vars, prefix)
}

fn find_hole_loop(
  vars: List(#(String, #(Value, Value))),
  prefix: String,
) -> Result(Value, Nil) {
  case vars {
    [] -> Error(Nil)
    [#(name, #(value, _)), ..rest] ->
      case string.starts_with(name, prefix) {
        True -> Ok(value)
        False -> find_hole_loop(rest, prefix)
      }
  }
}

// ── Neutral comparison ────────────────────────────────────────────

fn match_neutral(
  state: State,
  head1: Head,
  spine1: List(Elim),
  head2: Head,
  spine2: List(Elim),
) -> State {
  case head1, head2 {
    HVar(l1), HVar(l2) ->
      case l1 == l2 {
        True -> match_spines(state, spine1, spine2)
        False -> add_type_mismatch_error(
          state, VNeut(HVar(l1), spine1), VNeut(HVar(l2), spine2),
        )
      }
    HHole(id1), HHole(id2) ->
      case { id1 == id2 } && { list.length(spine1) == list.length(spine2) } {
        True -> match_spines(state, spine1, spine2)
        False -> add_type_mismatch_error(
          state, VNeut(HHole(id1), spine1), VNeut(HHole(id2), spine2),
        )
      }
    _, _ -> add_type_mismatch_error(
      state, VNeut(head1, spine1), VNeut(head2, spine2),
    )
  }
}

/// Match two neutral spines element by element.
fn match_spines(state: State, spine1: List(Elim), spine2: List(Elim)) -> State {
  case spine1, spine2 {
    [], [] -> state
    [EApp(arg1), EApp(arg2)], _ -> match_values(state, arg1, arg2)
    _, _ -> state
  }
}

// ── Record matching ───────────────────────────────────────────────

fn match_records(
  state: State,
  fields1: List(#(String, Value)),
  fields2: List(#(String, Value)),
) -> State {
  case fields1, fields2 {
    [], [] -> state
    [#(name1, val1), ..rest1], [#(name2, val2), ..rest2] ->
      case name1 == name2 {
        True -> match_records(
          match_values(state, val1, val2),
          rest1,
          rest2,
        )
        False -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
      }
    _, _ -> add_type_mismatch_error(state, VRcd(fields1), VRcd(fields2))
  }
}

// ── Occurs check ──────────────────────────────────────────────────

/// Check if a hole ID occurs in a value (for occurs check).
///
/// Always returns `False` to allow recursive types.
/// This is a deliberate design choice — Tao supports recursive types.
pub fn occurs_check(_level: Int, _value: Value) -> Bool {
  // Always return False to allow recursive types
  False
}

// ── Term unification (for Lambda/fixpoint bodies) ─────────────────

fn unify_terms(state: State, t1: Term, t2: Term) -> State {
  case t1, t2 {
    Var(i1, s1), Var(i2, s2) ->
      case i1 == i2, s1 == s2 {
        True, True -> state
        _, _ -> error_term(state, s1)
      }
    Hole(id1, s1), Hole(id2, s2) ->
      case id1 == id2, s1 == s2 {
        True, True -> state
        _, _ -> error_term(state, s1)
      }
    Lam(#(_, p1), b1, _), Lam(#(_, p2), b2, _) ->
      case unify_terms(state, p1, p2) {
        s -> unify_terms(s, b1, shift_term(b2, 1))
      }
    App(f1, a1, _), App(f2, a2, _) ->
      case unify_terms(state, f1, f2) {
        s -> unify_terms(s, a1, a2)
      }
    Pi(d1, c1, _), Pi(d2, c2, _) ->
      case unify_terms(state, d1, d2) {
        s -> unify_terms(s, c1, c2)
      }
    Lit(v1, s1), Lit(v2, s2) ->
      case v1 == v2, s1 == s2 {
        True, True -> state
        _, _ -> error_term(state, s1)
      }
    Ctr(t1, a1, s1), Ctr(t2, a2, s2) ->
      case t1 == t2, s1 == s2 {
        True, True -> unify_terms(state, a1, a2)
        _, _ -> error_term(state, s1)
      }
    Match(a1, c1, _s1), Match(a2, c2, _s2) ->
      case unify_terms(state, a1, a2) {
        s -> unify_cases(s, c1, c2)
      }
    Ann(t1, ty1, _), Ann(t2, ty2, _) ->
      case unify_terms(state, t1, t2) {
        s -> unify_terms(s, ty1, ty2)
      }
    Call(n1, a1, s1), Call(n2, a2, s2) ->
      case n1 == n2, s1 == s2 {
        True, True -> unify_term_list(state, a1, a2)
        _, _ -> error_term(state, s1)
      }
    Rcd(f1, s1), Rcd(f2, s2) ->
      case s1 == s2 {
        True -> unify_records(state, f1, f2)
        False -> error_term(state, s2)
      }
    Typ(l1, s1), Typ(l2, s2) ->
      case l1 == l2, s1 == s2 {
        True, True -> state
        _, _ -> error_term(state, s1)
      }
    Err(m1, s1), Err(m2, s2) ->
      case m1 == m2, s1 == s2 {
        True, True -> state
        _, _ -> error_term(state, s1)
      }
    _, _ -> error_term(state, case t1 {
      Var(_, s) | Hole(_, s) | Lit(_, s) | Typ(_, s) | Err(_, s) | Lam(_, _, s) -> s
      App(_, _, s) | Pi(_, _, s) | Ctr(_, _, s) | Match(_, _, s) -> s
      Ann(_, _, s) | Call(_, _, s) | Rcd(_, s) -> s
    })
  }
}

fn unify_cases(state: State, cases1: List(Case), cases2: List(Case)) -> State {
  case cases1, cases2 {
    [], [] -> state
    [Case(p1, g1, b1, s1), ..r1], [Case(p2, g2, b2, _s2), ..r2] -> {
      let s1 = case pattern_equal(p1, p2) {
        True -> state
        False -> error_term(state, s1)
      }
      let s2 = case g1, g2 {
        None, None -> s1
        _, _ -> unify_opt_term(s1, g1, g2)
      }
      unify_cases(unify_terms(s2, b1, b2), r1, r2)
    }
    _, _ -> error_term(state, case cases1 {
      [Case(_, _, _, s), ..] -> s
      [] -> single("", 0, 0)
    })
  }
}

fn unify_opt_term(state: State, t1: Option(Term), t2: Option(Term)) -> State {
  case t1, t2 {
    Some(a), Some(b) -> unify_terms(state, a, b)
    None, None -> state
    _, _ -> state
  }
}

fn pattern_equal(p1: Pattern, p2: Pattern) -> Bool {
  case p1, p2 {
    PAny(s1), PAny(s2) -> s1 == s2
    PVar(n1, s1), PVar(n2, s2) -> n1 == n2 && s1 == s2
    PCtr(t1, p1, s1), PCtr(t2, p2, s2) -> t1 == t2 && s1 == s2 && pattern_equal(p1, p2)
    PUnit(s1), PUnit(s2) -> s1 == s2
    PLit(v1, s1), PLit(v2, s2) -> v1 == v2 && s1 == s2
    _, _ -> False
  }
}

fn unify_term_list(state: State, ts1: List(Term), ts2: List(Term)) -> State {
  case ts1, ts2 {
    [], [] -> state
    [t1, ..r1], [t2, ..r2] -> unify_terms(unify_term_list(state, r1, r2), t1, t2)
    _, _ -> state
  }
}

fn unify_records(state: State, fields1: List(#(String, Term)), fields2: List(#(String, Term))) -> State {
  case fields1, fields2 {
    [], [] -> state
    [#(n1, v1), ..r1], [#(n2, v2), ..r2] ->
      case n1 == n2 {
        True -> unify_records(unify_terms(state, v1, v2), r1, r2)
        False -> state
      }
    _, _ -> state
  }
}

fn error_term(state: State, span: Span) -> State {
  with_err(state, TypeMismatch(VNeut(HHole(0), []), VNeut(HHole(1), []), span))
}

// ── Term shift (under a binder) ───────────────────────────────────

fn shift_term(term: Term, n: Int) -> Term {
  case term {
    Var(i, span) ->
      case i >= n {
        True -> Var(i + n, span)
        False -> Var(i, span)
      }
    Hole(id, span) -> Hole(id, span)
    Lam(#(name, param), func_body, span) ->
      Lam(#(name, shift_term(param, n)), shift_term(func_body, n + 1), span)
    App(fun, arg, span) ->
      App(shift_term(fun, n), shift_term(arg, n), span)
    Pi(domain, codomain, span) ->
      Pi(shift_term(domain, n), shift_term(codomain, n), span)
    Lit(value, span) -> Lit(value, span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term(arg, n), span)
    Match(arg, cases, span) ->
      Match(
        shift_term(arg, n),
        list.map(cases, fn(c) {
          Case(c.pattern, c.guard, shift_term(c.body, n), c.span)
        }),
        span,
      )
    Ann(t, type_, span) ->
      Ann(shift_term(t, n), shift_term(type_, n), span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { shift_term(a, n) }), span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(f) { #(f.0, shift_term(f.1, n)) }), span)
    Typ(level, span) -> Typ(level, span)
    Err(msg, span) -> Err(msg, span)
  }
}

/// Shift De Bruijn levels in a value by n.
fn shift_value(value: Value, n: Int) -> Value {
  case value {
    VNeut(head, spine) ->
      VNeut(shift_head(head, n), list.map(spine, fn(e) { shift_elim(e, n) }))
    VLam(#(name, param), body) ->
      VLam(#(name, shift_value(param, n)), shift_term(body, n + 1))
    VPi(domain, codomain) ->
      VPi(shift_value(domain, n), shift_value(codomain, n))
    VLit(value) -> VLit(value)
    VCtr(tag, arg) -> VCtr(tag, shift_value(arg, n))
    VRcd(fields) ->
      VRcd(list.map(fields, fn(f) { #(f.0, shift_value(f.1, n)) }))
    VErr -> VErr
  }
}

fn shift_head(head: Head, n: Int) -> Head {
  case head {
    HVar(level) -> HVar(level + n)
    HHole(id) -> HHole(id)
  }
}

fn shift_elim(e: Elim, n: Int) -> Elim {
  case e {
    EApp(arg) -> EApp(shift_value(arg, n))
  }
}

// ── Error helpers ─────────────────────────────────────────────────

fn add_type_mismatch_error(state: State, expected: Value, actual: Value) -> State {
  with_err(state, TypeMismatch(expected, actual, single("", 0, 0)))
}
