/// Normalization by Evaluation (NBE) — Term → Value

import core/ast.{
  type Term, type Value, type Case, type Pattern,
  Var, Hole, Lam, App, Pi, Lit, Ctr, Match, Ann, Call, Rcd, Typ, Err,
  VNeut, HHole, HVar, VLam, VPi, VLit, VCtr, VRcd, VErr, EApp,
  term_to_string,
  Case as CoreCase,
  PAny, PVar, PCtr as Pctr, PUnit, PLit,
  Int as LitInt, Float as LitFloat,
}
import core/state.{type State, State, lookup_ffi, FfiEntry}
import core/subst.{subst_term_var, force}
import gleam/list
import gleam/float
import gleam/int
import gleam/option.{Some, None}

// ============================================================================
// MAIN EVALUATION
// ============================================================================

/// Evaluate a `Term` to a `Value` using Normalization by Evaluation (NBE).
///
/// The evaluator recursively converts each term constructor to its
/// semantic value counterpart:
///
/// - `Var(n)` → `VNeut(HVar(n), [])` — variable becomes neutral
/// - `Hole(id)` → `VNeut(HHole(id), [])` — hole becomes neutral
/// - `Lam` → `VLam` — lambda becomes a closure (body is already a Term)
/// - `App` → apply argument to evaluated function via `do_app`
/// - `Pi` → `VPi` — type-level, evaluated domain/codomain
/// - `Lit` → `VLit` — literal values
/// - `Ctr` → `VCtr` — constructor wrapping
/// - `Rcd` → `VRcd` — record with evaluated fields
/// - `Ann` → just evaluate the term (annotation is erased)
/// - `Match` → evaluate scrutinee, dispatch to matching case body
/// - `Call` → look up FFI builtin and apply
/// - `Err` → `VErr` — error term
///
/// The returned `Value` may still contain unresolved holes. The `force`
/// function from `subst.gleam` can be used to resolve them.
///
/// ## Example
///
/// ```gleam
/// import core/eval.{evaluate}
/// import core/state.{initial_state}
/// import core/ast.{Lit, LitInt, Rcd}
///
/// let state = initial_state([])
/// let value = evaluate(state, Lit(LitInt(42), ?))
/// // value == VLit(LitInt(42))
/// ```
pub fn evaluate(state: State, term: Term) -> Value {
  case term {
    Var(index, _) -> VNeut(HVar(index), [])
    Hole(id, _) -> VNeut(HHole(id), [])
    Lam(#(name, param_type), body, _span) -> {
      // Evaluate the parameter type term to a value, then force to
      // resolve any holes in it. The body remains as a Term (closure).
      let param_val = force(state, evaluate(state, param_type))
      VLam(#(name, param_val), body)
    }
    App(fun, arg, _) -> {
      let fun_val = evaluate(state, fun)
      let arg_val = evaluate(state, arg)
      do_app(state, fun_val, arg_val)
    }
    Pi(domain, codomain, _) -> {
      // Evaluate domain to a value. The codomain references the domain
      // at type level — no shift needed since Pi doesn't create a runtime
      // variable binding.
      let dom = evaluate(state, domain)
      let codom = evaluate(state, codomain)
      VPi(dom, codom)
    }
    Lit(value, _) -> VLit(value)
    Ctr(tag, arg, _) -> VCtr(tag, evaluate(state, arg))
    Rcd(fields, _) -> VRcd(list.map(fields, fn(f) { #(f.0, evaluate(state, f.1)) }))
    Ann(term, _, _) -> evaluate(state, term)
    Match(arg, cases, _) -> {
      let scrutinee = evaluate(state, arg)
      do_match(scrutinee, cases, [])
    }
    Call(name, args, _) -> {
      // Evaluate all arguments
      let eval_args = list.map(args, fn(a) { evaluate(state, a) })
      // Look up FFI entry
      case lookup_ffi(state, name) {
        Ok(FfiEntry(fn_name: _, impl: impl_fn)) ->
          case impl_fn(list.map(eval_args, fn(v) { #(v, VNeut(HHole(0), [])) })) {
            Some(result) -> result
            None -> VErr
          }
        Error(_) -> VErr
      }
    }
    Typ(level, _) -> VNeut(HVar(level), [])
    Err(msg, _) -> {
      let _ = msg
      VErr
    }
  }
}

// ============================================================================
// APPLICATION — Neutral spine construction and beta reduction
// ============================================================================

/// Apply an evaluated argument to an evaluated function.
///
/// This is the core of NBE application. It handles:
///
/// 1. **Lambda application** — β-reduction: substitute the argument into
///    the body, then evaluate (force) the result.
/// 2. **Neutral spine** — if the function is already neutral (variable,
///    hole, or application), extend its spine with the argument.
/// 3. **Error propagation** — if the function is `VErr`, result is `VErr`.
/// 4. **Type mismatch** — if the function is a type (VPi, VCtr, etc.)
///    rather than a value that accepts arguments, record an error.
///
/// ## Example
///
/// ```gleam
/// // Identity function applied to 42
/// let fn_val = VLam(#("x", VRcd([])), Var(0, empty))
/// let arg_val = VLit(LitInt(42))
/// let result = do_app(fn_val, arg_val)
/// // result == VLam(#("x", VRcd([])), VLit(LitInt(42))) after force
/// ```
pub fn do_app(state: State, fun_val: Value, arg_val: Value) -> Value {
  case fun_val {
    // β-reduction: substitute the argument for the lambda parameter, then
    // evaluate the body. The body's indices are already relative to this
    // lambda — no shift needed.
    VLam(_param, body) -> {
      // The body's Var(0) refers to the lambda parameter at the current scope.
      // Substitute Var(0) with the argument value (converted to a Term).
      // No shift needed — the body's indices are already relative to this lambda.
      let substituted = subst_term_var(0, arg_val, body)
      evaluate(state, substituted)
    }
    // Extend neutral spine: variable or hole applied to argument
    VNeut(head, spine) -> VNeut(head, list.append(spine, [EApp(arg_val)]))
    // Error propagates
    VErr -> VErr
    // Cannot apply a type/value that isn't a function — return error
    VPi(_, _) | VCtr(_, _) | VLit(_) | VRcd(_) -> VErr
  }
}

// ============================================================================
// MATCH — Pattern matching on values
// ============================================================================

/// Evaluate a match expression.
///
/// Evaluates the scrutinee to a value, then tries each case pattern
/// in order. The first matching case body is evaluated (in the pattern-
/// bound environment extended with the original state's variables).
///
/// ## Example
///
/// ```gleam
/// // Match on #Some(42)
/// let cases = [
///   Case(PCtr("Just", PVar("v"), span), None, Var(0, span), span),
///   Case(PCtr("Nothing", PAny(span), span), None, Var(1, span), span),
/// ]
/// let scrutinee = Ctr("Some", Lit(LitInt(42), span), span)
/// // evaluates to the first case body with "v" bound
/// ```
fn do_match(scrutinee: Value, cases: List(Case), bindings: List(#(String, Value))) -> Value {
  case cases {
    [] -> VErr
    [CoreCase(pattern, guard, body, _case_span), ..rest] -> {
      case match_pattern(pattern, scrutinee, bindings) {
        Ok(env_bindings) -> {
          // Evaluate optional guard
          case guard {
            Some(guard_term) -> {
              // Guard must evaluate to unit (empty record) to pass
              let guard_val = evaluate(match_state(env_bindings), guard_term)
              let is_true = is_true_value(guard_val)
              case is_true {
                True -> evaluate(match_state(env_bindings), body)
                False -> do_match(scrutinee, rest, bindings)
              }
            }
            None -> evaluate(match_state(env_bindings), body)
          }
        }
        Error(Nil) -> do_match(scrutinee, rest, bindings)
      }
    }
  }
}

/// Create a temporary state with pattern-matched bindings for evaluation.
/// The type field (`VNeut(HHole(0), [])`) is a placeholder — never used
/// by the evaluator since type checking happens before evaluation.
fn match_state(bindings: List(#(String, Value))) -> State {
  // Use a minimal state — bindings are used via pattern env, not state lookup
  State(
    vars: list.map(bindings, fn(b) { #(b.0, #(b.1, VNeut(HHole(0), []))) }),
    errors: [],
    ffi: [],
    hole_counter: 0,
  )
}

/// Check if a value is considered "true" for guard evaluation.
///
/// A guard passes if it evaluates to:
/// - A non-empty record (truthy)
/// - A neutral term (assumed truthy)
/// - A constructor (assumed truthy — truth constructors are VCtr)
///
/// A guard fails if it evaluates to:
/// - An empty record (unit = falsity)
/// - VErr
pub fn is_true_value(value: Value) -> Bool {
  case value {
    VRcd(fields) -> fields != []  // Empty record = false, non-empty = true
    VCtr(_, _) -> True  // Constructors (like True) are truthy
    VNeut(_, _) -> True  // Neutral terms are assumed truthy
    _ -> False  // Literals, VPi, VErr are falsy
  }
}

// ============================================================================
// PATTERN MATCHING
// ============================================================================

/// Try to match a `Pattern` against a `Value`.
///
/// Returns the updated bindings with any new variable bindings from the
/// pattern (e.g., `PVar(name)` binds `name` to the matched value).
///
/// ## Patterns
///
/// - `PAny(_)` — matches anything, no bindings
/// - `PVar(name)` — matches anything, binds `name`
/// - `PCtr(tag, inner_pat)` — matches `VCtr(tag, val)` and recursively matches inner
/// - `PUnit` — matches `VRcd([])` (empty record)
/// - `PLit(value)` — matches `VLit(value)` of the same literal
///
/// ## Example
///
/// ```gleam
/// // Match #Some(42) against #Some(v)
/// let pattern = PCtr("Some", PVar("v"), span)
/// let value = VCtr("Some", VLit(LitInt(42)))
/// let bindings = match_pattern(pattern, value, [])
/// // Ok([#("v", VLit(LitInt(42)))])
/// ```
pub fn match_pattern(
  pattern: Pattern,
  value: Value,
  bindings: List(#(String, Value)),
) -> Result(List(#(String, Value)), Nil) {
  case pattern {
    PAny(_) -> Ok(bindings)
    PVar(name, _) -> Ok([#(name, value), ..bindings])
    Pctr(tag, inner, _) -> {
      case value {
        VCtr(tag2, arg_val) ->
          case tag == tag2 {
            True -> match_pattern(inner, arg_val, bindings)
            False -> Error(Nil)
          }
        _ -> Error(Nil)
      }
    }
    PUnit(_) -> {
      case value {
        VRcd([]) -> Ok(bindings)
        _ -> Error(Nil)
      }
    }
    PLit(lit, _) -> {
      case value {
        VLit(lit2) if lit == lit2 -> Ok(bindings)
        _ -> Error(Nil)
      }
    }
  }
}

/// Look up a variable name in the pattern-matching environment.
///
/// Returns the bound value, or a neutral variable reference if
/// not found in the pattern bindings.
pub fn lookup_env(name: String, bindings: List(#(String, Value))) -> Value {
  case list.find(bindings, fn(b) { b.0 == name }) {
    Ok(#(_, v)) -> v
    Error(_) -> VNeut(HVar(0), [])
  }
}

// ============================================================================
// STRING REPRESENTATION
// ============================================================================

/// Format an evaluation result as a human-readable string.
pub fn value_to_string(value: Value) -> String {
  case value {
    VNeut(head, spine) -> {
      let head_str = case head {
        HVar(level) -> "v" <> int.to_string(level)
        HHole(id) -> "?" <> int.to_string(id)
      }
      case spine {
        [] -> head_str
        _ -> {
          let spine_str = list.fold(
            spine, "", fn(acc, e) {
              let s = case e {
                EApp(arg) -> "(" <> value_to_string(arg) <> ")"
              }
              acc <> s
            },
          )
          head_str <> spine_str
        }
      }
    }
    VLam(#(name, _), body) -> "%fn(" <> name <> ") => " <> term_to_string(body)
    VPi(domain, codomain) ->
      "%fn(_) : " <> value_to_string(domain) <> " -> " <> value_to_string(codomain)
    VLit(lit) -> case lit {
      LitInt(v) -> int.to_string(v)
      LitFloat(v) -> float.to_string(v)
    }
    VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ -> "{" <> list.fold(fields, "", fn(acc, f) {
          case acc {
            "" -> f.0 <> ": " <> value_to_string(f.1)
            _ -> acc <> ", " <> f.0 <> ": " <> value_to_string(f.1)
          }
        }) <> "}"
      }
    VErr -> "\"error\""
  }
}
