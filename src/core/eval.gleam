/// Normalization by Evaluation (NbE) — Term → Value
///
/// Design philosophy: `eval` should be as *simple* as possible. It walks
/// the term and reduces what is mechanically reducible; it never
/// *checks* anything. All error detection belongs to `infer`/`check` (and
/// unification), so evaluating an expression that contains type errors is
/// basically *undefined behavior*: whatever `eval` produces in that case
/// is fine, and no guarantee is made about it. The correctness guarantee
/// is one-way — *if* infer/check report no errors, evaluation is
/// correct. Keeping `eval` free of semantic machinery (no type
/// definitions, no environment lookups beyond the term's own variables,
/// no error reporting) is what makes the rest of the compiler provable
/// in that sense: a value depends only on its term, never on the module
/// records or type definitions that happened to be in scope. For a
/// concrete example of this division of labor, see docs/overloads.md:
/// overload dispatch looks up type definitions at *compile* and *check*
/// time (`define.expand_overload_choices`, `unify`'s Ctr-vs-Typ rule) so
/// that the runtime match here stays a blind tag comparison.
import core/ffi.{type FFI}
import core/term.{type Case, type Pattern, type Term} as tm
import core/value.{type Env, type Type, type Value} as v
import gleam/list
import gleam/option.{None, Some}
import utils/list_utils.{at}

/// Normalize a Term to a Value by walking it and β-reducing where
/// possible. Anything depending on a hole or a variable is preserved as
/// a *neutral* value so it re-evaluates correctly once holes are solved.
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  eval_rec(ffi, env, term, 0)
}

// Bounds the eval↔quote cycle that never terminates on self-referential
// types (see docs/implicit-args.md, Limitations).
const max_depth = 10000

const depth_exceeded =
  "error: the compiler hit a deeply recursive type while simplifying (recursive implicit function types are not supported yet; see docs/implicit-args.md)"

fn eval_rec(ffi: FFI, env: Env, term: Term, depth: Int) -> Value {
  case depth > max_depth {
    True -> panic as depth_exceeded
    False -> eval_step(ffi, env, term, depth)
  }
}

fn eval_step(ffi: FFI, env: Env, term: Term, depth: Int) -> Value {
  case term {
    tm.Typ(universe) -> v.Typ(universe)
    tm.Hole(id) -> v.hole_open(env, id)
    tm.Lit(value) -> v.Lit(value)
    tm.LitT(value) -> v.LitT(value)
    tm.Var(index) ->
      case at(env, index) {
        Some(value) -> value
        None -> v.Err
      }
    tm.Ctr(tag, arg) -> v.Ctr(tag, eval_rec(ffi, env, arg, depth + 1))
    tm.Rcd(fields, tail) -> {
      let fields_val =
        list.map(fields, fn(field) {
          let #(name, #(term, default)) = field
          let value = eval_rec(ffi, env, term, depth + 1)
          let default_val = option.map(default, fn(d) { eval_rec(ffi, env, d, depth + 1) })
          #(name, #(value, default_val))
        })
      let tail_val = option.map(tail, fn(t) { eval_rec(ffi, env, t, depth + 1) })
      v.Rcd(fields_val, tail_val)
    }
    tm.Call(name, ret, arg) -> {
      let ret_val = eval_rec(ffi, env, ret, depth + 1)
      let arg_val = eval_rec(ffi, env, arg, depth + 1)
      do_call(ffi, name, ret_val, arg_val)
    }
    tm.Ann(term, _) -> eval_rec(ffi, env, term, depth + 1)
    tm.For(#(name, param), body) -> {
      let param_val = eval_rec(ffi, env, param, depth + 1)
      v.For(env, #(name, param_val), body)
    }
    tm.Lam(#(name, param), body) -> {
      let param_val = eval_rec(ffi, env, param, depth + 1)
      v.Lam(env, #(name, param_val), body)
    }
    tm.Pi(#(name, domain), codomain) -> {
      let domain_val = eval_rec(ffi, env, domain, depth + 1)
      v.Pi(env, #(name, domain_val), codomain)
    }
    tm.Fix(name, body) -> v.Fix(env, name, body)
    tm.App(fun, arg) -> {
      let fun_val = eval_rec(ffi, env, fun, depth + 1)
      let arg_val = eval_rec(ffi, env, arg, depth + 1)
      do_app_rec(ffi, fun_val, arg_val, depth + 1)
    }
    tm.TypeDef(tm.TypeDefinition(params, arg, variants)) -> {
      let param_vals =
        list.map(params, fn(param) {
          let #(name, typ) = param
          #(name, eval_rec(ffi, env, typ, depth + 1))
        })
      let p_env = v.env_push(env, list.length(params))
      let variant_vals =
        list.map(variants, fn(variant) {
          let #(tag, tm.Variant(vparams, varg, vret)) = variant
          let vparam_vals =
            list.map(vparams, fn(param) {
              let #(name, typ) = param
              #(name, eval_rec(ffi, p_env, typ, depth + 1))
            })
          #(tag, v.Variant(vparam_vals, varg, vret))
        })
      v.TypeDef(env, v.TypeDefinition(param_vals, arg, variant_vals))
    }
    tm.Match(arg, cases) -> {
      let arg_val = eval_rec(ffi, env, arg, depth + 1)
      do_match_rec(ffi, env, arg_val, cases, depth + 1)
    }
    tm.Err -> v.Err
  }
}

/// Apply a value to an argument. Neutral function heads stay neutral
/// (`NApp`); `For`/`Lam` β-reduce; `Fix` feeds itself as the argument.
pub fn do_app(ffi: FFI, fun_val: Value, arg_val: Value) -> Value {
  do_app_rec(ffi, fun_val, arg_val, 0)
}

fn do_app_rec(ffi: FFI, fun_val: Value, arg_val: Value, depth: Int) -> Value {
  case fun_val {
    // Neutral application
    v.Neut(neut_fun) -> v.app(neut_fun, arg_val)
    // Instantiation
    v.For(env, _, body) -> eval_rec(ffi, [arg_val, ..env], body, depth + 1)
    // Lambda application: β-reduction
    v.Lam(env, _, body) -> eval_rec(ffi, [arg_val, ..env], body, depth + 1)
    // Recursive function application
    v.Fix(env, _, body) -> {
      let body_val = eval_rec(ffi, [fun_val, ..env], body, depth + 1)
      do_app_rec(ffi, body_val, arg_val, depth + 1)
    }
    // Not a function
    _ -> v.Err
  }
}

/// Call a builtin by name: reduce via the FFI table if defined, otherwise
/// keep a neutral `NCall` (an `extern`, unresolvable at type-check time).
pub fn do_call(ffi: FFI, name: String, ret_val: Type, arg_val: Value) -> Value {
  let result = case list.key_find(ffi, name) {
    Ok(call_def) -> call_def(arg_val)
    Error(Nil) -> None
  }
  case result {
    Some(value) -> value
    None -> v.call(name, ret_val, arg_val)
  }
}

/// The outcome of matching one pattern against one value.
///
/// Pattern matching is *three-valued* so that a match whose outcome
/// depends on an unresolved neutral can be told apart from a match that
/// is decided not to match: a neutral field or tail may still turn out
/// to match, so the match is kept neutral (`NMatch`) and re-reduced once
/// the neutrals resolve, instead of baking in the wrong case or an `Err`.
pub type MatchResult(a) {
  /// The pattern matches; `a` carries the result (bindings or the
  /// accepted case).
  MatchAccept(a)
  /// The pattern is decided not to match: a shape or value mismatch that
  /// no resolution of the neutrals can change.
  MatchReject
  /// The outcome depends on a neutral that is not (yet) resolved.
  MatchNeutral
}

/// Reduce a match: try each case in order — the first accepted case
/// (with a satisfied guard) wins, rejected cases fall through, and a
/// neutral pattern or guard keeps the whole match neutral (`NMatch`,
/// capturing `env`) until the blocking neutrals resolve. `Err` is
/// returned only when every case is decided not to match.
pub fn do_match(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  cases: List(Case),
) -> Value {
  do_match_rec(ffi, env, arg_val, cases, 0)
}

fn do_match_rec(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  cases: List(Case),
  depth: Int,
) -> Value {
  case do_match_case_list(ffi, env, arg_val, cases, depth) {
    MatchAccept(#(case_, env)) -> eval_rec(ffi, env, case_.body, depth + 1)
    MatchReject -> v.Err
    MatchNeutral -> v.match(env, arg_val, cases)
  }
}

/// Try each case in order, returning the first accepted case with its
/// environment, `MatchReject` when no case matches, or `MatchNeutral`
/// when some case cannot be decided yet.
fn do_match_case_list(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  cases: List(Case),
  depth: Int,
) -> MatchResult(#(Case, Env)) {
  case cases {
    [] -> MatchReject
    [case_, ..cases] ->
      case do_match_case(ffi, env, arg_val, case_, depth) {
        MatchAccept(env) -> MatchAccept(#(case_, env))
        MatchReject -> do_match_case_list(ffi, env, arg_val, cases, depth)
        MatchNeutral -> MatchNeutral
      }
  }
}

/// Match one case's pattern (and guard, if any) against the scrutinee,
/// returning the environment with the pattern's bindings prepended.
fn do_match_case(
  ffi: FFI,
  env: Env,
  arg_val: Value,
  case_: Case,
  depth: Int,
) -> MatchResult(Env) {
  case match_pattern(case_.pattern, arg_val) {
    MatchAccept(bindings) -> {
      let env = list.append(bindings, env)
      case case_.guard {
        Some(guard) -> do_match_guard(ffi, env, guard, depth)
        None -> MatchAccept(env)
      }
    }
    MatchReject -> MatchReject
    MatchNeutral -> MatchNeutral
  }
}

/// Evaluate a case guard in the case environment and match its pattern
/// against the result. A neutral guard value keeps the case undecided.
fn do_match_guard(
  ffi: FFI,
  env: Env,
  guard: #(Term, Pattern),
  depth: Int,
) -> MatchResult(Env) {
  let #(guard_term, guard_pattern) = guard
  let guard_value = eval_rec(ffi, env, guard_term, depth + 1)
  case match_pattern(guard_pattern, guard_value) {
    MatchAccept(bindings) -> MatchAccept(list.append(bindings, env))
    MatchReject -> MatchReject
    MatchNeutral -> MatchNeutral
  }
}

/// Match a pattern against a value, returning `MatchAccept` (with the
/// bindings in innermost-first order), `MatchReject`, or `MatchNeutral`
/// when the outcome depends on an unresolved neutral. Record fields are
/// matched in pattern order; a field absent from the value's head is
/// searched for in its tail, which must be a record.
pub fn match_pattern(
  pattern: Pattern,
  value: Value,
) -> MatchResult(List(Value)) {
  case pattern, value {
    // Decidable acceptances...
    tm.PAny, _ -> MatchAccept([])
    tm.PTyp(u1), v.Typ(u2) if u1 == u2 -> MatchAccept([])
    tm.PLit(k1), v.Lit(k2) if k1 == k2 -> MatchAccept([])
    tm.PLitT(k1), v.LitT(k2) if k1 == k2 -> MatchAccept([])
    tm.PAlias(_, pattern), _ ->
      case match_pattern(pattern, value) {
        MatchAccept(bindings) -> MatchAccept([value, ..bindings])
        MatchReject -> MatchReject
        MatchNeutral -> MatchNeutral
      }
    // A constructor tag is always decidable; only its argument may not
    // be, so a tag mismatch rejects even against a neutral argument.
    tm.PCtr(tag1, pattern), v.Ctr(tag2, arg) if tag1 == tag2 ->
      match_pattern(pattern, arg)
    tm.PRcd([], None), v.Rcd([], None) -> MatchAccept([])
    tm.PRcd([], Some(ptail)), value -> match_pattern(ptail, value)
    tm.PRcd([#(name, pat), ..pfields], ptail), value ->
      case match_pattern_rcd_field(name, pat, value) {
        MatchAccept(#(bindings, value)) ->
          case match_pattern(tm.PRcd(pfields, ptail), value) {
            MatchAccept(ys) -> MatchAccept(list.append(ys, bindings))
            MatchReject -> MatchReject
            MatchNeutral -> MatchNeutral
          }
        MatchReject -> MatchReject
        MatchNeutral -> MatchNeutral
      }
    tm.PErr, v.Err -> MatchAccept([])
    // ...anything not decided above depends on a neutral value that may
    // still turn out to match (a neutral can resolve to any value).
    _, v.Neut(_) -> MatchNeutral
    // ...or is a decided mismatch.
    _, _ -> MatchReject
  }
}

/// Find one record field and match it, returning the bindings and the
/// *remaining* record (field removed; tail left intact or peeled into a
/// record tail), so subsequent fields keep matching positionally. A
/// neutral tail is `MatchNeutral`: the field may be in there once the
/// tail resolves.
fn match_pattern_rcd_field(
  name: String,
  pattern: Pattern,
  value: Value,
) -> MatchResult(#(List(Value), Value)) {
  case value {
    v.Rcd(vfields, opt_vtail) ->
      case tm.pop_field(vfields, name) {
        Some(#(#(value, _default), vfields)) ->
          case match_pattern(pattern, value) {
            MatchAccept(bindings) ->
              MatchAccept(#(bindings, v.Rcd(vfields, opt_vtail)))
            MatchReject -> MatchReject
            MatchNeutral -> MatchNeutral
          }
        None ->
          case opt_vtail {
            None -> MatchReject
            Some(vtail) ->
              case match_pattern_rcd_field(name, pattern, vtail) {
                MatchAccept(#(bindings, vrest)) ->
                  MatchAccept(#(bindings, v.Rcd(vfields, Some(vrest))))
                MatchReject -> MatchReject
                MatchNeutral -> MatchNeutral
              }
          }
      }
    // A neutral scrutinee: the field may be there once it resolves.
    v.Neut(_) -> MatchNeutral
    _ -> MatchReject
  }
}
