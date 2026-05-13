/// Normalization by Evaluation (NBE) - Term → Value
import core/ast.{
  type Case, type Pattern, type Term, type Value, type LiteralType,
  Ann, App, Call,
  Case as CoreCase, Ctr, EApp, EMatch, Err, Fix, Float as LitFloat, HHole, HFix, HVar, Hole,
  Int as LitInt, Lam, Lit, Match, PAny, PCtr as Pctr, PLit, PLitT, PUnit, PVar, PAlias, PTyp, PRcd, PError, Pi, Rcd, RcdT,
  Typ, VCtr, VCall, VFix, VErr, VLam, VLit, VNeut, VPi, VRcd, VRcdT, VTyp, VTypeDef, TypeDef, Var, term_to_string,  literal_type_to_string, VLitT, pattern_to_string,
  LitT, shift_term_from,
  IntT, FloatT, I8T, I16T, I32T, I64T, U8T, U16T, U32T, U64T, F16T, F32T, F64T,
}
import core/state.{State, type State, type FfiEntry as FfiEntryType, FfiEntry, lookup_ffi, state_to_env, env_to_state}
import syntax/span.{type Span}
import core/subst.{force, subst_term_var}
import gleam/float
import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/string

// ============================================================================
// MAIN EVALUATION
// ============================================================================

/// Convert a Term-level TypeDef constructor to a Value-level constructor.
/// Passes through the bindings field unchanged.
fn term_ctor_to_value(_state: State, ctor: #(String, List(String), Term, Term, Span)) -> #(String, List(String), Value, Value, Span) {
  let #(tag, bindings, _, _, span) = ctor
  #(tag, bindings, VNeut(HHole(0), []), VNeut(HHole(0), []), span)
}

/// Evaluate a `Term` to a `Value` using Normalization by Evaluation (NBE).
///
/// The evaluator recursively converts each term constructor to its
/// semantic value counterpart:
///
/// - `Var(n)` → `VNeut(HVar(n), [])` - variable becomes neutral
/// - `Hole(id)` → `VNeut(HHole(id), [])` - hole becomes neutral
/// - `Lam` → `VLam` - lambda becomes a closure (body is already a Term)
/// - `App` → apply argument to evaluated function via `do_app`
/// - `Pi` → `VPi` - type-level, evaluated domain/codomain
/// - `Lit` → `VLit` - literal values
/// - `Ctr` → `VCtr` - constructor wrapping
/// - `Rcd` → `VRcd` - record with evaluated fields
/// - `Ann` → just evaluate the term (annotation is erased)
/// - `Match` → evaluate scrutinee, dispatch to matching case body
/// - `Call` → look up FFI builtin and apply
/// - `Err` → `VErr` - error term
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
    Var(index, _) ->
      case list.drop(state.vars, index) {
        [#(_, #(value, _)), ..] -> value
        _ -> force(state_to_env(state), VNeut(HVar(index), []), do_match)
      }
    Hole(id, _) -> force(state_to_env(state), VNeut(HHole(id), []), do_match)
    Lam(implicits, #(name, param_type), body, _span) -> {
      // Evaluate the parameter type term to a value, then force to
      // resolve any holes in it. The body remains as a Term (closure).
      let env = state_to_env(state)
      let param_val = force(env, evaluate(state, param_type), do_match)
      let implicit_env = list.map(implicits, fn(i) {
        let ival = force(env, evaluate(state, i.1), do_match)
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
      // at type level - no shift needed since Pi doesn't create a runtime
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
    RcdT(fields, _) -> {
      let typed_fields = list.map(fields, fn(f) {
        let field_type = evaluate(state, f.1)
        let default_val = case f.2 {
          Some(d) -> Some(evaluate(state, d))
          None -> None
        }
        #(f.0, field_type, default_val)
      })
      VRcdT(typed_fields)
    }
    LitT(ltype, _) -> VLitT(ltype)
    Ctr(tag, arg, _) -> VCtr(tag, evaluate(state, arg))
    Rcd(fields, _) ->
      VRcd(list.map(fields, fn(f) { #(f.0, evaluate(state, f.1)) }))
    Ann(term, _, _) -> evaluate(state, term)
    Match(arg, cases, _) -> {
      let scrutinee = evaluate(state, arg)
      let env = state_to_env(state)
      case scrutinee {
        VNeut(head, spine) -> {
          // Scrutinee is neutral - defer the match by appending EMatch to the spine
          // force() will resolve the head and apply the spine (including EMatch)
          force(env, VNeut(head, list.append(spine, [EMatch(env, cases)])), do_match)
        }
        VFix(fix_name, fix_env, fix_body) -> {
          // VFix is a deferred value - defer the match by treating it as neutral
          // Pass VFix directly to HFix - no name lookup needed
          let vfix_val = VFix(fix_name, fix_env, fix_body)
          force(env, VNeut(HFix(vfix_val), [EMatch(env, cases)]), do_match)
        }
        _ -> do_match(env, state.truth_ctr, state.ffi, scrutinee, cases, [])
      }
    }
    Call(name, args, return_type, _span) -> {
      // Evaluate each (value_term, type_term) pair
      let arg_vals = list.map(args, fn(ta) { evaluate(state, ta.0) })
      let arg_types = list.map(args, fn(ta) { evaluate(state, ta.1) })
      let arg_pairs = list.map2(arg_vals, arg_types, fn(v, t) { #(v, t) })

      // Evaluate return type
      let ret_type_val = evaluate(state, return_type)

      // Look up FFI entry
      case lookup_ffi(state, name) {
        Ok(FfiEntry(fn_name: _, impl: impl_fn)) ->
          case impl_fn(arg_pairs) {
            Some(result) -> result
            None -> VCall(name, arg_pairs, ret_type_val)
          }
        Error(_) -> VCall(name, arg_pairs, ret_type_val)
      }
    }
    Typ(level, _) -> VTyp(level)
    TypeDef(name: n, params: p, constructors: c, span: _) -> {
      // Evaluate params to values
      let value_params = list.map(p, fn(param) {
        #(param.0, evaluate(state, param.1))
      })
      let value_constructors = list.map(c, fn(ctor) { term_ctor_to_value(state, ctor) })
      VTypeDef(name: n, params: value_params, constructors: value_constructors)
    }
    Fix(name, body, _) -> {
      // $fix f. body evaluates to a VFix value.
      // Shift body by -1 so that the fix variable (at Var(2) after term_to_debruijn
      // due to pattern variable shadowing) becomes Var(1) relative to the VLam's
      // parameter. This matches what infer_fix does.
      let shifted_body = shift_term_from(body, -1, 1)
      VFix(name, [], shifted_body)
    }
    Err(_, _) -> VErr
  }
}

// ============================================================================
// APPLICATION - Neutral spine construction and beta reduction
// ============================================================================

/// Apply an evaluated argument to an evaluated function.
///
/// This is the core of NBE application. It handles:
///
/// 1. **Lambda application** - β-reduction: substitute the argument into
///    the body, then evaluate (force) the result.
/// 2. **Neutral spine** - if the function is already neutral (variable,
///    hole, or application), extend its spine with the argument.
/// 3. **Error propagation** - if the function is `VErr`, result is `VErr`.
/// 4. **Type mismatch** - if the function is a type (VPi, VCtr, etc.)
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
    // lambda - no shift needed.
    VLam(_env, _implicits, #(pname, param_type), body) -> {
      // Convert int to float when param type is FloatT
      let converted_arg = case param_type {
        VLitT(FloatT) -> case arg_val {
          VLit(LitInt(v)) -> {
            // Convert int to float by parsing the string representation
            case float.parse(int.to_string(v) <> ".0") {
              Ok(f) -> VLit(LitFloat(f))
              Error(_) -> arg_val
            }
          }
          _ -> arg_val
        }
        _ -> arg_val
      }
      // The body's Var(0) refers to the lambda parameter at the current scope.
      // Extend state with the parameter so that Var(0) resolves to arg_val,
      // and Var(1), Var(2), etc. resolve to outer variables from the
      // enclosing $let bindings (which are in state.vars).
      let new_var = #(pname, #(converted_arg, VNeut(HHole(0), [])))
      let extended = state.State(
        ..state,
        vars: list.append([new_var], state.vars),
      )
      let substituted = subst_term_var(0, converted_arg, body)
      evaluate(extended, substituted)
    }
    // VFix unroll: substitute the argument for Var(0) (Lambda param) and
    // the VFix for Var(1) (recursive ref), then evaluate.
    // This follows the rule: Fix(e) → e[Fix(e)/0], shifted through the
    // Lambda binder so Var(1) in the Match body refers to the Fix.
    //
    // Key: value_to_neut converts VFix→Fix(term) in subst.gleam, so
    // substitution preserves the fixpoint as a term-level construct.
    VFix(fix_name, fix_env, fix_body) -> {
      let body = case fix_body {
        Ann(inner, _, _) -> inner
        _ -> fix_body
      }
      case body {
        Lam(_implicits, param, body_term, _) -> {
          // Convert int to float when param type is FloatT
          let converted_arg = case param.1 {
            Ann(typ, _, _) -> case typ {
              LitT(FloatT, _) -> case arg_val {
                VLit(LitInt(v)) -> {
                  case float.parse(int.to_string(v) <> ".0") {
                    Ok(f) -> VLit(LitFloat(f))
                    Error(_) -> arg_val
                  }
                }
                _ -> arg_val
              }
              _ -> arg_val
            }
            LitT(FloatT, _) -> case arg_val {
              VLit(LitInt(v)) -> {
                case float.parse(int.to_string(v) <> ".0") {
                  Ok(f) -> VLit(LitFloat(f))
                  Error(_) -> arg_val
                }
              }
              _ -> arg_val
            }
            _ -> arg_val
          }
          // Step 1: Substitute the argument for Var(0) in the Lambda's body
          let body_with_arg = subst_term_var(0, converted_arg, body_term)
          // Step 2: Substitute the VFix for Var(1) (recursive reference)
          // value_to_neut converts VFix→Fix(term), preserving the fixpoint
          let self = VFix(fix_name, fix_env, fix_body)
          let body_with_self = subst_term_var(1, self, body_with_arg)
          // Evaluate the fully substituted body
          evaluate(state, body_with_self)
        }
        _ -> VErr
      }
    }
    // Extend neutral spine: variable or hole applied to argument
    // The spine is ordered FIFO (first applied first), so append new EApp
    VNeut(head, spine) -> VNeut(head, list.append(spine, [EApp(arg_val)]))
    // Error propagates
    VErr -> VErr
    // Cannot apply a type/value that isn't a function - return error
    VCall(_, _, _) -> VErr
    VPi(_, _, _, _) | VCtr(_, _) | VLit(_) | VRcd(_) | VRcdT(_) | VTypeDef(name: _, params: _, constructors: _) | VTyp(_) | VLitT(_) -> VErr
  }
}

// ============================================================================
// MATCH - Pattern matching on values
// ============================================================================

/// Evaluate a match expression.
///
/// Evaluates the scrutinee to a value, then tries each case pattern
/// in order. The first matching case body is evaluated (in the pattern-
/// bound environment extended with the original state's variables).
///
/// The `truth_ctr` parameter specifies the constructor name that
/// represents truth in guards (e.g., `"True"`). A guard passes if it
/// evaluates to `#<truth_ctr>(...)` - any other value is falsy.
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
  env: List(Value),
  truth_ctr: String,
  ffi: List(FfiEntryType),
  scrutinee: Value,
  cases: List(Case),
  bindings: List(#(String, Value)),
) -> Value {
  // Handle VFix scrutinee by unrolling and recursively matching
  let scrutinee = case scrutinee {
    VFix(fix_name, fix_env, fix_body) -> {
      // Unroll VFix: get the lambda body and evaluate param type
      let body = case fix_body {
        Ann(inner, _, _) -> inner
        _ -> fix_body
      }
      case body {
        Lam(_implicits, param, body_term, _) -> {
          let param_val = case param.1 {
            Ann(t, _, _) -> evaluate(env_to_state(env, truth_ctr, ffi), t)
            _ -> evaluate(env_to_state(env, truth_ctr, ffi), param.1)
          }
          // Create VLam and match against it
          let lam_val = VLam(fix_env, [], #(param.0, param_val), body_term)
          // Self-apply: the VFix is a fixed point, so we need to
          // match the lambda body after substituting the VFix for the recursive ref
          do_match(env, truth_ctr, ffi, lam_val, cases, bindings)
        }
        _ -> VErr
      }
    }
    _ -> scrutinee
  }

  // If scrutinee is still VFix after unrolling, return VErr (no match)
  case scrutinee {
    VFix(_, _, _) -> VErr
    _ -> case cases {
      [] -> VErr
      [CoreCase(pattern, guard, body, _case_span), ..rest] -> {
        case match_pattern(pattern, scrutinee, bindings) {
          Ok(env_bindings) -> {
            // Convert env_bindings (List(#(String, Value))) to List(Value)
            let env_with_bindings = list.append(env, list.map(env_bindings, fn(b) { b.1 }))
            // Evaluate optional guard
            case guard {
              Some(guard_term) -> {
                let guard_val =
                  evaluate(env_to_state(env_with_bindings, truth_ctr, ffi), guard_term)
                case is_truth(truth_ctr, guard_val) {
                  True -> evaluate(env_to_state(env_with_bindings, truth_ctr, ffi), body)
                  False -> do_match(env, truth_ctr, ffi, scrutinee, rest, bindings)
                }
              }
              None -> evaluate(env_to_state(env_with_bindings, truth_ctr, ffi), body)
            }
          }
          Error(Nil) -> do_match(env, truth_ctr, ffi, scrutinee, rest, bindings)
        }
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
/// The type field (`VNeut(HHole(0), [])`) is a placeholder - never used
/// by the evaluator since type checking happens before evaluation.
fn match_state(
  bindings: List(#(String, Value)),
  truth_ctr: String,
  outer_vars: List(#(String, #(Value, Value))),
) -> State {
  // Pattern bindings shadow outer variables, so they come first
  let pattern_vars = list.map(bindings, fn(b) { #(b.0, #(b.1, VNeut(HHole(0), []))) })
  State(
    vars: list.append(pattern_vars, outer_vars),
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
/// - `PAny(_)` - matches anything, no bindings
/// - `PVar(name)` - matches anything, binds `name`
/// - `PCtr(tag, inner_pat)` - matches `VCtr(tag, val)` and recursively matches inner
/// - `PUnit` - matches `VRcd([])` (empty record)
/// - `PLit(value)` - matches `VLit(value)` of the same literal
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
    PAlias(alias_name, inner, _) -> {
      case match_pattern(inner, value, bindings) {
        Ok(new_bindings) -> Ok([#(alias_name, value), ..new_bindings])
        Error(_) -> Error(Nil)
      }
    }
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
    PLitT(lit_type, _) -> {
      // PLitT patterns match literal type values (e.g., $Int, $Float)
      case value {
        VLitT(t) ->
          case t == lit_type {
            True -> Ok(bindings)
            False -> Error(Nil)
          }
        // Wildcard type matching on literal values (legacy)
        VLit(ast.Int(_)) ->
          case lit_type {
            IntT -> Ok(bindings)
            _ -> Error(Nil)
          }
        VLit(ast.Float(_)) ->
          case lit_type {
            FloatT -> Ok(bindings)
            _ -> Error(Nil)
          }
        _ -> Error(Nil)
      }
    }
    PTyp(universe, _) -> {
      // PTyp patterns match higher-order type values (e.g., $Type, $Type<1>)
      case value {
        VTyp(0) -> Ok(bindings)
        VTyp(n) if n == universe -> Ok(bindings)
        VPi(_, _, _, _) -> Ok(bindings)
        VTypeDef(_, _, _) -> Ok(bindings)
        VNeut(HHole(_), _) -> Ok(bindings)
        VNeut(HVar(_), _) -> Ok(bindings)
        VCtr(tag, _) ->
          case tag {
            "Type" -> Ok(bindings)
            _ -> Error(Nil)
          }
        _ -> Error(Nil)
      }
    }
    PRcd(fields, _) -> {
      case value {
        VRcd(record_fields) -> {
          // Check that all pattern fields exist in the record
          case do_match_rcd(fields, record_fields, bindings) {
            Ok(result) -> Ok(result)
            Error(_) -> Error(Nil)
          }
        }
        VRcdT(rcdt_fields) -> {
          // Match record type pattern against record type value.
          // Extract just (name, type) pairs from VRcdT fields for matching.
          let rcd_type_fields = list.map(rcdt_fields, fn(f) { #(f.0, f.1) })
          case do_match_rcd(fields, rcd_type_fields, bindings) {
            Ok(result) -> Ok(result)
            Error(_) -> Error(Nil)
          }
        }
        _ -> Error(Nil)
      }
    }
    PError(_) -> {
      // Error patterns match on error terms
      case value {
        VErr -> Ok(bindings)
        _ -> Error(Nil)
      }
    }
  }
}

/// Helper: recursively match record fields against record values
fn do_match_rcd(
  fields: List(#(String, Pattern)),
  record_fields: List(#(String, Value)),
  bindings: List(#(String, Value)),
) -> Result(List(#(String, Value)), Nil) {
  case fields {
    [] -> Ok(bindings)
    [first, ..rest] -> {
      case list.find(record_fields, fn(r) { r.0 == first.0 }) {
        Ok(#(_, val)) ->
          case match_pattern(first.1, val, bindings) {
            Ok(new_bindings) -> do_match_rcd(rest, record_fields, new_bindings)
            Error(_) -> Error(Nil)
          }
        Error(_) -> Error(Nil)
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
// TYPE PATTERN MATCHING (GADT-style constructor checking)
// ============================================================================

/// Match a type pattern (Value) against an argument type (Value).
///
/// Returns Option(Env) — Some(env) with bindings if matching succeeds,
/// None if matching fails (pattern mismatch).
///
/// The returned env contains bindings for pattern variables (holes) that
/// were filled during matching. These bindings are short-lived and used
/// immediately for evaluating result_type terms.
///
/// ## Pattern types handled
///
/// - **Holes** (`VNeut(HHole(id), [])`): Bind the hole to the arg type
/// - **Literal types** (`VLitT(IntT)`, `VLitT(FloatT)`, etc.): Check arg type unifies
/// - **Constructor types** (`VCtr(tag, arg)`): Check arg type matches by tag
/// - **Record types** (`VRcd([...])`): Check each field recursively
/// - **Record types with defaults** (`VRcdT([...])`): Fill in missing
///   fields from defaults before matching
///
/// ## Example
///
/// ```gleam
/// // Match IntT against IntT
/// let pattern = VLitT(IntT)
/// let arg = VLitT(IntT)
/// let result = match_type_pattern(pattern, arg, [])
/// // Some([])
///
/// // Match any type against a hole (binds the hole)
/// let pattern = VNeut(HHole(0), [])
/// let arg = VLitT(IntT)
/// let result = match_type_pattern(pattern, arg, [])
/// // Some([#("hole_0", VLitT(IntT))])
/// ```
pub fn match_type_pattern(
  type_pattern: Value,
  arg_type: Value,
  bindings: List(#(String, Value)),
) -> Option(List(#(String, Value))) {
  case type_pattern, arg_type {
    // Hole in pattern: bind it to the arg type
    VNeut(HHole(id), []), _ ->
      case list.find(bindings, fn(b) { b.0 == "hole_" <> int.to_string(id) }) {
        Ok(_) -> Some(bindings)  // Already bound
        Error(_) -> Some([#("hole_" <> int.to_string(id), arg_type), ..bindings])
      }

    // VLitT literal type: check arg type unifies
    VLitT(ptag), VLitT(atag) ->
      case ptag == atag {
        True -> Some(bindings)
        False -> None
      }
    // Wildcard: $Int matches any integer literal type
    VLitT(IntT), _ ->
      case arg_type {
        VLitT(IntT) | VLitT(I8T) | VLitT(I16T) | VLitT(I32T) | VLitT(I64T) |
        VLitT(U8T) | VLitT(U16T) | VLitT(U32T) | VLitT(U64T) -> Some(bindings)
        _ -> None
      }
    // Wildcard: $Float matches any float literal type AND integer literal types
    VLitT(FloatT), _ ->
      case arg_type {
        VLitT(FloatT) | VLitT(F16T) | VLitT(F32T) | VLitT(F64T) |
        VLitT(IntT) | VLitT(I8T) | VLitT(I16T) | VLitT(I32T) | VLitT(I64T) |
        VLitT(U8T) | VLitT(U16T) | VLitT(U32T) | VLitT(U64T) -> Some(bindings)
        _ -> None
      }
    // VCtr: same tag check (legacy support)
    VCtr(tag, _), VCtr(tag2, _) if tag == tag2 -> Some(bindings)
    // VCtr: $Int wildcard matches integer type constructors
    VCtr("Int", _), VCtr(tag2, _) ->
      case tag2 {
        "I8" | "I16" | "I32" | "I64" | "U8" | "U16" | "U32" | "U64" | "Int" ->
          Some(bindings)
        _ -> None
      }
    // VCtr: $Float wildcard matches float type constructors and integers
    VCtr("Float", _), VCtr(tag2, _) ->
      case tag2 {
        "F16" | "F32" | "F64" | "Int" | "I8" | "I16" | "I32" | "I64" |
        "U8" | "U16" | "U32" | "U64" | "Float" ->
          Some(bindings)
        _ -> None
      }

    // Record type: check each field recursively
    VRcd(fields), VRcd(arg_fields) ->
      match_record_type_fields(fields, arg_fields, bindings)

    // Record type with defaults: fill in missing fields, then match
    VRcdT(rcdt_fields), VRcd(arg_fields) -> {
      // Extract just (name, type) pairs from VRcdT fields
      let rcd_type_fields = list.map(rcdt_fields, fn(f) { #(f.0, f.1) })
      let filled = fill_rcdt_defaults(rcdt_fields, arg_fields)
      match_record_type_fields(rcd_type_fields, filled, bindings)
    }

    // Other types: try to unify (conservative match)
    _, _ ->
      case type_pattern {
        // Type variable matches anything
        VNeut(HHole(_), _) | VNeut(HVar(_), _) | VTyp(_) | VPi(_, _, _, _) | VTypeDef(_, _, _) ->
          Some(bindings)
        // Error: no match
        _ -> None
      }
  }
}

/// Fill in missing fields from VRcdT defaults.
///
/// If a field is missing from the arg value but has a default in the
/// type pattern, the default is used. If the arg provides a different
/// value than the default, the arg's value takes precedence.
/// Defaults only apply when the field is *missing* from the arg value.
/// When a field is missing and has no default, use VErr as a sentinel.
fn fill_rcdt_defaults(
  rcdt_fields: List(#(String, Value, Option(Value))),
  arg_fields: List(#(String, Value)),
) -> List(#(String, Value)) {
  let arg_map = list.map(arg_fields, fn(f) { #(f.0, f.1) })
  list.map(rcdt_fields, fn(f) {
    let #(name, _type_val, default_val) = f
    case list.find(arg_map, fn(a) { a.0 == name }) {
      Ok(#(_, arg_val)) -> #(name, arg_val)  // Arg provides value
      Error(_) -> case default_val {
        Some(def_val) -> #(name, def_val)  // Use default
        None -> #(name, VErr)  // No default, field is missing
      }
    }
  })
}

/// Match record type fields against argument type fields.
fn match_record_type_fields(
  fields: List(#(String, Value)),
  arg_fields: List(#(String, Value)),
  bindings: List(#(String, Value)),
) -> Option(List(#(String, Value))) {
  case fields {
    [] -> Some(bindings)
    [first, ..rest] -> {
      case list.find(arg_fields, fn(r) { r.0 == first.0 }) {
        Ok(#(_, arg_val)) ->
          case match_type_pattern(first.1, arg_val, bindings) {
            Some(new_bindings) -> match_record_type_fields(rest, arg_fields, new_bindings)
            None -> None
          }
        Error(_) -> None  // Field missing in arg type
      }
    }
  }
}

// ============================================================================
// TYPE PATTERN MATCHING HELPERS
// ============================================================================

/// Check if a literal type matches a type pattern name.
///
/// PTyp("Int", _) matches $Int, $I8-$I64, $U8-$U64 (wildcard matching).
/// PTyp("Float", _) matches $Float, $F16-$F64.
/// PTyp("I8", _) matches $I8 and $Int.
/// PTyp("I16", _) matches $I16 and $Int.
/// etc.
fn ptype_matches(type_name: String, t: LiteralType) -> Bool {
  case t {
    IntT -> list.contains(["Int", "I8", "I16", "I32", "I64", "U8", "U16", "U32", "U64"], type_name)
    FloatT -> list.contains(["Float", "F16", "F32", "F64"], type_name)
    I8T -> list.contains(["I8", "Int"], type_name)
    I16T -> list.contains(["I16", "Int"], type_name)
    I32T -> list.contains(["I32", "Int"], type_name)
    I64T -> list.contains(["I64", "Int"], type_name)
    U8T -> list.contains(["U8", "Int"], type_name)
    U16T -> list.contains(["U16", "Int"], type_name)
    U32T -> list.contains(["U32", "Int"], type_name)
    U64T -> list.contains(["U64", "Int"], type_name)
    F16T -> list.contains(["F16", "Float"], type_name)
    F32T -> list.contains(["F32", "Float"], type_name)
    F64T -> list.contains(["F64", "Float"], type_name)
  }
}

// ============================================================================
// STRING REPRESENTATION
// ============================================================================

/// Format an evaluation result as a human-readable string.
/// Debug: print a value as a string for inspection.
/// Returns "__VErr__" for errors, otherwise delegates to eval_value_to_string.
pub fn debug_value(value: Value) -> String {
  case value {
    VErr -> "__VErr__"
    _ -> eval_value_to_string(value)
  }
}

pub fn eval_value_to_string(value: Value) -> String {
  case value {
    VNeut(head, spine) -> {
      let head_str = case head {
        HVar(level) -> "v" <> int.to_string(level)
        HHole(id) -> "?" <> int.to_string(id)
        HFix(vfix) -> case vfix {
          VFix(name, _, _) -> "$fix " <> name
          _ -> "$fix ?"
        }
      }
      case spine {
        [] -> head_str
        _ -> {
          let spine_str =
            list.fold(spine, "", fn(acc, e) {
              let s = case e {
                EApp(arg) -> "(" <> eval_value_to_string(arg) <> ")"
                EMatch(_env, cases) -> " {" <> list.fold(cases, "", fn(acc, c) {
                  acc <> " | " <> pattern_to_string(c.pattern) <> " => " <> term_to_string(c.body)
                }) <> " }"
              }
              acc <> s
            })
          head_str <> spine_str
        }
      }
    }
    VLam(_env, _implicits, #(name, _param), body) -> "$fn(" <> name <> ") => " <> term_to_string(body)
    VPi(_env, _implicits, domain, codomain) ->
      "<>"
      <> "#(_) : "
      <> eval_value_to_string(domain.1)
      <> " -> "
      <> eval_value_to_string(codomain)
    VLit(lit) ->
      case lit {
        LitInt(v) -> int.to_string(v)
        LitFloat(v) -> float.to_string(v)
      }
    VCtr(tag, arg) -> "#" <> tag <> "(" <> eval_value_to_string(arg) <> ")"
    VRcd(fields) ->
      case fields {
        [] -> "()"
        _ ->
          "{" 
          <> list.fold(fields, "", fn(acc, f) {
            case acc {
              "" -> f.0 <> ": " <> eval_value_to_string(f.1)
              _ -> acc <> ", " <> f.0 <> ": " <> eval_value_to_string(f.1)
            }
          })
          <> "}"
      }
    VRcdT(fields) ->
      "$" 
      <> "{" 
      <> list.fold(fields, "", fn(acc, f) {
        let field_str = f.0 <> ": " <> eval_value_to_string(f.1)
        let with_default = case f.2 {
          Some(d) -> field_str <> " = " <> eval_value_to_string(d)
          None -> field_str
        }
        case acc {
          "" -> with_default
          _ -> acc <> ", " <> with_default
        }
      })
      <> "}"
    VCall(name, args, return_type) -> {
      let arg_strs = list.map(args, fn(a) {
        eval_value_to_string(a.0) <> ": " <> eval_value_to_string(a.1)
      })
      "%" <> name <> "(" <> string.join(arg_strs, ", ") <> ") -> " <> eval_value_to_string(return_type)
    }
    VFix(name, _env, body) ->
      "VFix(" <> name <> " => " <> term_to_string(body) <> ")"
    VErr -> "\"error\""
    VTypeDef(name: _, params: _, constructors: _) -> "<type _>"
    VTyp(level) -> "$Type<" <> int.to_string(level) <> ">"
    VLitT(t) -> literal_type_to_string(t)
  }
}
