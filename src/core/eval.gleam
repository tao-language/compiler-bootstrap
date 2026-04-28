/// Normalization by Evaluation (NBE) — Term → Value
import core/ast.{
  type Case, type Pattern, type Term, type Value, Ann, App, Call,
  Case as CoreCase, Ctr, EApp, Err, Float as LitFloat, HHole, HVar, Hole,
  Int as LitInt, Lam, Lit, Match, PAny, PCtr as Pctr, PLit, PUnit, PVar, Pi, Rcd,
  Typ, VCtr, VErr, VLam, VLit, VNeut, VPi, VRcd, VTypeDef, TypeDef, Var, term_to_string,
}
import core/state.{type State, FfiEntry, State, lookup_ffi}
import syntax/span.{type Span}
import core/subst.{force, subst_term_var}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{None, Some}

// ============================================================================
// MAIN EVALUATION
// ============================================================================

/// Convert a Term-level TypeDef param to a Value-level param.
/// Just wraps the term in a neutral value for now.
fn term_param_to_value(state: State, param: #(String, Term)) -> #(String, Value) {
  let #(name, _) = param
  #(name, VNeut(HHole(0), []))
}

/// Convert a Term-level TypeDef constructor to a Value-level constructor.
/// Just wraps the terms in neutral values for now.
fn term_ctor_to_value(state: State, ctor: #(String, Term, Term, Span)) -> #(String, Value, Value, Span) {
  let #(tag, _, _, span) = ctor
  #(tag, VNeut(HHole(0), []), VNeut(HHole(0), []), span)
}

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
    Lam(implicits, #(name, param_type), body, _span) -> {
      // Evaluate the parameter type term to a value, then force to
      // resolve any holes in it. The body remains as a Term (closure).
      let param_val = force(state, evaluate(state, param_type))
      let env = list.map(state.vars, fn(v) { v.1.0 })
      let implicit_env = list.map(implicits, fn(i) {
        let ival = force(state, evaluate(state, i.1))
        #(i.0, ival)
      })
      VLam(env, implicit_env, #(name, param_val), body)
    }
    App(fun, arg, _) -> {
      let fun_val = evaluate(state, fun)
      let arg_val = evaluate(state, arg)
      do_app(state, fun_val, arg_val)
    }
    Pi(implicits, #(name, domain), codomain, _) -> {
      // Evaluate domain to a value. The codomain references the domain
      // at type level — no shift needed since Pi doesn't create a runtime
      // variable binding.
      let env = list.map(state.vars, fn(v) { v.1.0 })
      let dom = evaluate(state, domain)
      let codom = evaluate(state, codomain)
      let implicit_env = list.map(implicits, fn(i) {
        let ival = evaluate(state, i.1)
        #(i.0, ival)
      })
      VPi(env, implicit_env, #(name, dom), codom)
    }
    Lit(value, _) -> VLit(value)
    Ctr(tag, arg, _) -> VCtr(tag, evaluate(state, arg))
    Rcd(fields, _) ->
      VRcd(list.map(fields, fn(f) { #(f.0, evaluate(state, f.1)) }))
    Ann(term, _, _) -> evaluate(state, term)
    Match(arg, cases, _) -> {
      let scrutinee = evaluate(state, arg)
      do_match(state.truth_ctr, scrutinee, cases, [])
    }
    Call(name, args, typed_args, return_type, span) -> {
      // Evaluate all arguments
      let eval_args = list.map(args, fn(a) { evaluate(state, a) })
      // Look up FFI entry
      case lookup_ffi(state, name) {
        Ok(FfiEntry(fn_name: _, impl: impl_fn)) ->
          case
            impl_fn(list.map(eval_args, fn(v) { #(v, VNeut(HHole(0), [])) }))
          {
            Some(result) -> result
            None -> VErr
          }
        Error(_) -> VErr
      }
    }
    Typ(level, _) -> VNeut(HVar(level), [])
    TypeDef(name: n, params: p, constructors: c, span: _) -> {
      let value_params = list.map(p, fn(param) { term_param_to_value(state, param) })
      let value_constructors = list.map(c, fn(ctor) { term_ctor_to_value(state, ctor) })
      VTypeDef(name: n, params: value_params, constructors: value_constructors)
    }
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
    VLam(_env, _implicits, #(_pname, _param_type), body) -> {
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
    VPi(_, _, _, _) | VCtr(_, _) | VLit(_) | VRcd(_) | VTypeDef(name: _, params: _, constructors: _) -> VErr
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
/// The `truth_ctr` parameter specifies the constructor name that
/// represents truth in guards (e.g., `"True"`). A guard passes if it
/// evaluates to `#<truth_ctr>(...)` — any other value is falsy.
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
fn do_match(
  truth_ctr: String,
  scrutinee: Value,
  cases: List(Case),
  bindings: List(#(String, Value)),
) -> Value {
  case cases {
    [] -> VErr
    [CoreCase(pattern, guard, body, _case_span), ..rest] -> {
      case match_pattern(pattern, scrutinee, bindings) {
        Ok(env_bindings) -> {
          // Evaluate optional guard
          case guard {
            Some(guard_term) -> {
              let guard_val =
                evaluate(match_state(env_bindings, truth_ctr), guard_term)
              case is_truth(truth_ctr, guard_val) {
                True -> evaluate(match_state(env_bindings, truth_ctr), body)
                False -> do_match(truth_ctr, scrutinee, rest, bindings)
              }
            }
            None -> evaluate(match_state(env_bindings, truth_ctr), body)
          }
        }
        Error(Nil) -> do_match(truth_ctr, scrutinee, rest, bindings)
      }
    }
  }
}

/// Check if a value matches the truth constructor.
///
/// A guard evaluates to true if it produces a constructor whose tag
/// matches the configured `truth_ctr` (e.g., `#True(...)`).
pub fn is_truth(truth_ctr: String, value: Value) -> Bool {
  case value {
    VCtr(tag, _) -> tag == truth_ctr
    _ -> False
  }
}

/// Create a temporary state with pattern-matched bindings for evaluation.
/// The type field (`VNeut(HHole(0), [])`) is a placeholder — never used
/// by the evaluator since type checking happens before evaluation.
fn match_state(bindings: List(#(String, Value)), truth_ctr: String) -> State {
  State(
    vars: list.map(bindings, fn(b) { #(b.0, #(b.1, VNeut(HHole(0), []))) }),
    errors: [],
    ffi: [],
    hole_counter: 0,
    truth_ctr: truth_ctr,
  )
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
          let spine_str =
            list.fold(spine, "", fn(acc, e) {
              let s = case e {
                EApp(arg) -> "(" <> value_to_string(arg) <> ")"
              }
              acc <> s
            })
          head_str <> spine_str
        }
      }
    }
    VLam(_env, _implicits, #(name, _param), body) -> "%fn(" <> name <> ") => " <> term_to_string(body)
    VPi(_env, _implicits, domain, codomain) ->
      "<>"
      <> "#(_) : "
      <> value_to_string(domain.1)
      <> " -> "
      <> value_to_string(codomain)
    VLit(lit) ->
      case lit {
        LitInt(v) -> int.to_string(v)
        LitFloat(v) -> float.to_string(v)
      }
    VCtr(tag, arg) -> "#" <> tag <> "(" <> value_to_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ ->
          "{"
          <> list.fold(fields, "", fn(acc, f) {
            case acc {
              "" -> f.0 <> ": " <> value_to_string(f.1)
              _ -> acc <> ", " <> f.0 <> ": " <> value_to_string(f.1)
            }
          })
          <> "}"
      }
    VErr -> "\"error\""
    VTypeDef(name: _, params: _, constructors: _) -> "<type _>"
  }
}
