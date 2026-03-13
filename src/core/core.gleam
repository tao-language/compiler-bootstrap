import gleam/int
import gleam/list
import gleam/option.{type Option, None, Some}
import gleam/result
import gleam/string
import syntax/grammar.{type Span, Span}

// ============================================================================
// SYNTAX (Terms)
// ============================================================================

/// Terms represent the raw Abstract Syntax Tree (AST) as written by the
/// programmer. They use De Bruijn INDICES for variables.
///
/// For detailed documentation see:
/// - [Core Language Specification](../../docs/core.md#syntax-terms)
/// - [Normalization by Evaluation](../../docs/core.md#normalization-by-evaluation)
pub type Term {
  Term(data: TermData, span: Span)
}

pub type TermData {
  /// Universe type at level k. See docs/core.md for details.
  Typ(universe: Int)

  /// Literal value (42, 3.14, "hello"). Note: true/false are constructors.
  Lit(value: Literal)

  /// Literal type (I32, F64, etc.)
  LitT(typ: LiteralType)

  /// Bound variable (De Bruijn index). Index = distance to binder.
  Var(index: Int)

  /// Metavariable (hole) to be solved during type checking.
  Hole(id: Int)

  /// Error placeholder - used when parsing fails, allows error recovery
  Err(message: String)

  /// Record with named fields.
  Rcd(fields: List(#(String, Term)))

  /// Constructor application (e.g., Some(42), Cons(1, Nil)).
  Ctr(tag: String, arg: Term)

  /// Field projection (record.field).
  Dot(arg: Term, field: String)

  /// Type annotation (term : type).
  Ann(term: Term, typ: Term)

  /// Lambda abstraction (λx. body) with optional implicit type params.
  /// implicit: list of type parameter names (e.g., ["a", "b"] for <a, b>)
  /// param: #(name, type_annotation) for the single explicit parameter
  Lam(implicit: List(String), param: #(String, Term), body: Term)

  /// Dependent function type with implicit type params
  /// implicit: list of type parameter names (e.g., ["T", "U"] for <T, U>)
  /// name: value parameter name
  /// in: domain type
  /// out: codomain type (can mention name)
  Pi(implicit: List(String), name: String, in_term: Term, out_term: Term)

  /// Function application (f x) with optional implicit type args.
  /// implicit: list of type arguments (e.g., [I32, F32] for <I32, F32>)
  /// arg: single explicit argument
  App(fun: Term, implicit: List(Term), arg: Term)

  /// Pattern matching with dependent return type.
  Match(arg: Term, motive: Term, cases: List(Case))

  /// Built-in function call (FFI).
  Call(name: String, args: List(Term))

  /// Compile-time evaluation block.
  Comptime(term: Term)

  /// Fixpoint operator for recursion (fix f -> body).
  Fix(name: String, body: Term)
}

// ============================================================================
// SEMANTICS (Values)
// ============================================================================
// Values represent the evaluated, runtime form of terms. They use De Bruijn
// LEVELS for variables, where the level is the absolute order of creation.
// This makes substitution stable (no need to shift indices when moving terms).

pub type Value {
  /// Evaluated universe type
  VTyp(universe: Int)
  /// Evaluated literal value
  VLit(value: Literal)
  /// Evaluated literal type
  VLitT(typ: LiteralType)
  /// Neutral term: stuck on a variable or hole with pending operations
  VNeut(head: Head, spine: List(Elim))
  /// Evaluated record
  VRcd(fields: List(#(String, Value)))
  /// Evaluated constructor
  VCtr(tag: String, arg: Value)
  /// Closure: lambda with captured environment and implicit type params
  VLam(implicit: List(String), name: String, env: Env, body: Term)
  /// Dependent function type with implicit type params and evaluated domain
  VPi(implicit: List(String), name: String, env: Env, in_val: Value, out_term: Term)
  /// Record type with named fields
  VRecord(fields: List(#(String, Value)))
  /// Built-in function call deferred to runtime
  /// Created when FFI not found during eval, or when args are not concrete
  VCall(name: String, args: List(Value))
  /// Fixpoint value for recursion (self-referential closure)
  VFix(name: String, env: Env, body: Term)
  /// Error value for error recovery (continues checking after errors)
  VErr
}

pub type Type =
  Value

// ============================================================================
// PATTERNS
// ============================================================================
// Patterns for match expressions and let-bindings.

pub type Pattern {
  /// Wildcard pattern (_) - matches anything, doesn't bind
  PAny
  /// As-pattern (x @ pattern) - binds the matched value
  PAs(pattern: Pattern, name: String)
  /// Type pattern (Type_k)
  PTyp(universe: Int)
  /// Literal pattern (42)
  PLit(value: Literal)
  /// Literal type pattern (I32)
  PLitT(value: LiteralType)
  /// Record pattern {x = p, y = q}
  PRcd(fields: List(#(String, Pattern)))
  /// Constructor pattern (Cons p)
  PCtr(tag: String, arg: Pattern)
}

// ============================================================================
// NEUTRAL TERMS
// ============================================================================

/// Neutral terms represent computations stuck on unknowns (variables or holes).
/// The head is the variable/hole, and the spine is a list of pending operations.
///
/// ## Role in Normalization by Evaluation (NbE)
///
/// When evaluation encounters an unknown value, it can't reduce further.
/// Instead of failing, it builds a neutral term that records:
/// - What we're stuck on (the head)
/// - What operations are waiting (the spine/eliminations)
///
/// When the unknown becomes known (via unification), we "force" the neutral
/// term by replaying all pending operations on the now-known value.
///
/// For detailed documentation see:
/// - [Neutral Terms](../../docs/core.md#neutral-terms)
/// - [Normalization by Evaluation](../../docs/core.md#normalization-by-evaluation)
pub type Head {
  /// Variable head (De Bruijn level - absolute, stable).
  HVar(level: Int)
  /// Hole/metavariable head (to be solved by unification).
  HHole(id: Int)
}

/// Eliminators (spine operations) for neutral terms.
///
/// These are DELAYED operations that will be replayed when the neutral value
/// becomes known. Critical for NbE correctness.
///
/// ## Why EMatch is Essential
///
/// `EMatch` is CRITICAL for dependent pattern matching. When matching on a
/// neutral value, we can't reduce, so we store the match in the spine:
///
/// ```gleam
/// do_match(env, VNeut(head, spine), motive, cases)
///   = VNeut(head, [EMatch(env, motive, cases), ..spine])
/// ```
///
/// When the value becomes known, we replay the match.
/// Without `EMatch`, neutral terms with pending matches would be lost,
/// breaking NbE correctness. **DO NOT REMOVE**.
pub type Elim {
  /// Field projection: wait to project `.field` from a record.
  EDot(name: String)

  /// Function application: wait to apply function to argument.
  EApp(arg: Value)

  /// Implicit type application: wait to apply function to type argument.
  EAppImplicit(value: Value)

  /// Pattern matching: wait to match value against patterns.
  /// CRITICAL for NbE - DO NOT REMOVE.
  EMatch(env: Env, motive: Value, cases: List(Case))
}

pub type Case {
  Case(pattern: Pattern, body: Term, guard: Option(Term), span: Span)
}

// ============================================================================
// LITERALS
// ============================================================================

pub type Literal {
  I32(value: Int)
  I64(value: Int)
  U32(value: Int)
  U64(value: Int)
  F32(value: Float)
  F64(value: Float)
}

pub type LiteralType {
  I32T
  I64T
  U32T
  U64T
  F32T
  F64T
}

// ============================================================================
// CONSTRUCTOR DEFINITIONS
// ============================================================================
// Constructors can have type parameters and GADT-style return types.
// The ret_ty can mention the params, enabling indexed types.

pub type CtrDef {
  CtrDef(params: List(String), arg_ty: Term, ret_ty: Term)
}

pub type CtrEnv =
  List(#(String, CtrDef))

pub type CtrIndex =
  List(#(String, CtrEnv))

// ============================================================================
// ENVIRONMENTS AND STATE
// ============================================================================

pub type Env =
  List(Value)

/// Typing context: maps variable names to their (value, type) pairs.
/// Used during type checking to track bound variables and their types.
pub type Context =
  List(#(String, #(Value, Type)))

/// Substitution: maps hole IDs to their solved values.
/// Accumulated during unification to solve metavariables.
pub type Subst =
  List(#(Int, Value))

/// Type checking state, threading counters, contexts, and error accumulation.
pub type State {
  State(
    /// Next fresh hole ID for metavariables
    hole: Int,
    /// Next fresh variable level for De Bruijn levels
    var: Int,
    /// Constructor definitions (global environment)
    ctrs: CtrEnv,
    /// Typing context (local variables)
    ctx: Context,
    /// Substitution (solved metavariables)
    sub: Subst,
    /// Accumulated errors (for error recovery and IDE feedback)
    errors: List(Error),
    /// Host FFI registry (for built-in evaluation)
    ffi: FFI,
    /// Compiler configuration (permissions, target, etc.)
    config: Config,
  )
}

// ============================================================================
// COMPILER CONFIGURATION
// ============================================================================
// Configuration for compilation target and permissions.

/// Compiler configuration
pub type Config {
  Config(
    /// Target backend module name (e.g., "backend/javascript")
    target: String,
    permissions: List(Permission),
  )
}

/// Default compiler configuration
pub const default_config = Config(target: "backend/javascript", permissions: [])

/// Create initial state with default configuration, builtins, and predefined constructors.
pub const initial_state = State(
  hole: 0,
  var: 0,
  ctrs: [],
  // No predefined constructors - to be defined in prelude
  ctx: [],
  sub: [],
  errors: [],
  ffi: ffi_build,
  config: default_config,
)

// ============================================================================
// HOST FFI AND BUILT-INS
// ============================================================================
// Host FFIs allow built-in functions to execute during elaboration.
// This supports both pure operations (arithmetic) and impure operations
// (file I/O, environment variables) with permission checking.

/// Permission for compile-time operations
pub type Permission {
  AllowRead(path: String)
  AllowWrite(path: String)
}

/// Host FFI function definition
/// The impl function returns None when arguments are not concrete (deferred to runtime)
pub type Builtin {
  Builtin(
    impl: fn(List(Value)) -> Option(Value),
    required_permissions: List(Permission),
  )
}

/// Host FFI registry
pub type FFI =
  List(#(String, Builtin))

/// Default FFI built-ins - pure functions available at compile-time and runtime.
/// These are the standard arithmetic, comparison, and logical operations.
pub const ffi_build = [
  // Arithmetic (pure, always allowed)
  #("add", Builtin(add_impl, [])),
  #("sub", Builtin(sub_impl, [])),
  #("mul", Builtin(mul_impl, [])),
  #("div", Builtin(div_impl, [])),
  #("mod", Builtin(mod_impl, [])),

  // Comparison (pure)
  #("eq", Builtin(eq_impl, [])),
  #("neq", Builtin(neq_impl, [])),
  #("lt", Builtin(lt_impl, [])),
  #("lte", Builtin(lte_impl, [])),
  #("gt", Builtin(gt_impl, [])),
  #("gte", Builtin(gte_impl, [])),

  // Logical (pure)
  #("and", Builtin(and_impl, [])),
  #("or", Builtin(or_impl, [])),
  #("not", Builtin(not_impl, [])),
]

// ============================================================================
// BUILTIN IMPLEMENTATIONS
// ============================================================================
// All builtin implementations return Option(Value):
// - Some(result) when arguments are concrete and computation succeeds
// - None when arguments are not concrete (deferred to runtime)

pub fn add_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a + b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a +. b)))
    _ -> None
  }
}

pub fn sub_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a - b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a -. b)))
    _ -> None
  }
}

pub fn mul_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(a * b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a *. b)))
    _ -> None
  }
}

pub fn div_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] if b != 0 -> Some(VLit(I32(a / b)))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(a /. b)))
    _ -> None
  }
}

pub fn mod_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] if b != 0 -> Some(VLit(I32(a % b)))
    _ -> None
  }
}

pub fn eq_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a == b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a == b))))
    _ -> None
  }
}

pub fn neq_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a != b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a != b))))
    _ -> None
  }
}

pub fn lt_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a < b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a <. b))))
    _ -> None
  }
}

pub fn lte_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a <= b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a <=. b))))
    _ -> None
  }
}

pub fn gt_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a > b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a >. b))))
    _ -> None
  }
}

pub fn gte_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(a >= b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(a >=. b))))
    _ -> None
  }
}

pub fn and_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] ->
      Some(VLit(I32(bool_to_int(a != 0 && b != 0))))
    _ -> None
  }
}

pub fn or_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] ->
      Some(VLit(I32(bool_to_int(a != 0 || b != 0))))
    _ -> None
  }
}

pub fn not_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a))] -> Some(VLit(I32(bool_to_int(a == 0))))
    _ -> None
  }
}

fn bool_to_int(b: Bool) -> Int {
  case b {
    True -> 1
    False -> 0
  }
}

// ============================================================================
// COMPTIME HOST EVALUATION
// ============================================================================
// Host evaluation executes built-in functions during elaboration.
// This supports both pure operations (arithmetic) and impure operations
// (file I/O, environment variables) with permission checking.

/// Check if a required permission is granted.
/// Permissions match if:
/// - The permission types are the same, AND
/// - The granted permission is "*" (wildcard), OR
/// - The paths/values match exactly
/// - A granted Write permission fulfills a Read request, but not the other way around.
pub fn check_permission(required: Permission, granted: Permission) -> Bool {
  case required, granted {
    AllowRead(req), AllowRead(grant) -> req == grant || grant == "*"
    AllowRead(req), AllowWrite(grant) -> req == grant || grant == "*"
    AllowWrite(req), AllowWrite(grant) -> req == grant || grant == "*"
    AllowWrite(_), AllowRead(_) -> False
  }
}

/// Check if all required permissions are granted.
pub fn all_permissions_granted(
  required: List(Permission),
  granted: List(Permission),
) -> Bool {
  list.all(required, fn(r) {
    list.any(granted, fn(g) { check_permission(r, g) })
  })
}

/// Evaluate a term at compile-time (host evaluation).
///
/// This is used for `comptime` blocks. It executes built-in functions
/// with permission checking and returns the result.
///
/// Unknown built-ins or non-concrete args return VCall (deferred to runtime).
/// Permission errors add ComptimePermissionDenied to State.errors.
pub fn comptime_eval(s: State, term: Term) -> #(Value, State) {
  case term.data {
    Call(name, args) -> {
      case list.key_find(s.ffi, name) {
        Ok(Builtin(impl, required_perms)) -> {
          // Check permissions
          case all_permissions_granted(required_perms, s.config.permissions) {
            True -> {
              // Evaluate arguments
              let #(arg_vals, _, s1) = infer_args(s, args)

              // Execute (pure function) - returns None for non-concrete args
              case impl(arg_vals) {
                Some(result) -> #(result, s1)
                None -> {
                  // Arguments not concrete - defer to runtime
                  #(VCall(name, arg_vals), s1)
                }
              }
            }
            False -> {
              let err =
                ComptimePermissionDenied(name, term.span, required_perms)
              #(VErr, with_err(s, err))
            }
          }
        }
        Error(Nil) -> {
          // Unknown FFI - return VCall (deferred to runtime)
          let #(arg_vals, _, s1) = infer_args(s, args)
          #(VCall(name, arg_vals), s1)
        }
      }
    }

    // Recursively evaluate other terms
    _ -> {
      let #(val, _, s1) = infer(s, term)
      #(val, s1)
    }
  }
}

// ============================================================================
// EXHAUSTIVENESS CHECKING
// ============================================================================
// Pattern heads for the matrix algorithm (Maranget's algorithm).

type PMatrix =
  List(List(Pattern))

pub type PHead {
  HAny
  HTyp(universe: Int)
  HLit(value: Literal)
  HLitT(value: LiteralType)
  HRcd(fields: List(String))
  HCtr(name: String)
}

// ============================================================================
// ERRORS
// ============================================================================
// Error types for type checking and exhaustiveness checking.
// Errors are accumulated in State rather than thrown, enabling IDE support.

pub type Error {
  // Syntax errors
  SyntaxError(span: Span, expected: String, got: String, context: String)

  // Type errors
  PatternMismatch(pattern: Pattern, expected_ty: Type, s1: Span, s2: Span)
  TypeMismatch(expected: Type, got: Type, span1: Span, span2: Span)
  InfiniteType(hole_id: Int, ty: Type, span1: Span, span2: Span)
  NotAFunction(fun: Term, fun_ty: Value)
  VarUndefined(index: Int, span: Span)
  RcdMissingFields(name: List(String), span: Span)
  CtrUndefined(tag: String, span: Span)
  CtrUnsolvedParam(tag: String, ctr: CtrDef, id: Int, span: Span)
  DotFieldNotFound(name: String, fields: List(#(String, Value)), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  HoleUnsolved(id: Int, span: Span)
  SpineMismatch(span1: Span, span2: Span)
  ArityMismatch(span1: Span, span2: Span)
  TODO(message: String)

  // Exhaustiveness checks
  MatchRedundantCase(Span)
  MatchMissingCase(Span, Pattern)

  // Comptime errors
  ComptimePermissionDenied(
    operation: String,
    span: Span,
    required: List(Permission),
  )
}

// ============================================================================
// EVALUATION
// ============================================================================
// Evaluates a Term to a Value in the given environment.
// This is the "normalization" part of Normalization by Evaluation.

/// Evaluate a term to its normal form in the given environment.
///
/// The environment maps De Bruijn indices to values. When evaluating:
/// - Variables look up their index in the environment
/// - Lambdas become closures (capturing the current environment)
/// - Applications evaluate the function and argument, then apply
/// - Neutral terms are created when computation is stuck on unknowns
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  case term.data {
    Typ(k) -> VTyp(k)
    Lit(k) -> VLit(k)
    LitT(k) -> VLitT(k)
    Var(i) ->
      case list_get(env, i) {
        Some(value) -> value
        None -> VErr
      }
    Hole(id) -> VNeut(HHole(id), [])
    Rcd(fields) ->
      VRcd(list.map(fields, fn(kv) { #(kv.0, eval(ffi, env, kv.1)) }))
    Ctr(tag, arg) -> VCtr(tag, eval(ffi, env, arg))
    Dot(arg, name) -> do_dot(eval(ffi, env, arg), name)
    Ann(term, _) -> eval(ffi, env, term)
    Lam(implicit, param, body) -> {
      let #(name, _) = param
      VLam(implicit, name, env, body)
    }
    Pi(implicit, name, in_term, out_term) -> VPi(implicit, name, env, eval(ffi, env, in_term), out_term)
    App(fun, implicit, arg) -> {
      // Evaluate function and argument
      let fun_val = eval(ffi, env, fun)
      let arg_val = eval(ffi, env, arg)
      
      // Handle implicit arguments recursively
      case implicit {
        [] -> {
          // Base case: no implicit args, apply normally
          do_app(ffi, fun_val, arg_val)
        }
        [implicit_arg, ..rest] -> {
          // Recursive case: peel off one implicit arg
          let implicit_val = eval(ffi, env, implicit_arg)
          // Instantiate function with implicit and recurse
          let instantiated = do_app_implicit(fun_val, implicit_val)
          do_app_with_implicit(ffi, instantiated, rest, arg_val)
        }
      }
    }
    Match(arg, motive, cases) -> {
      let arg_val = eval(ffi, env, arg)
      let motive_val = eval(ffi, env, motive)
      do_match(env, arg_val, motive_val, cases)
    }
    Call(name, args) -> {
      // Evaluate all arguments first
      let arg_vals = list.map(args, eval(ffi, env, _))
      // Look up the builtin and call it
      case list.key_find(ffi, name) {
        Ok(Builtin(impl, _)) -> {
          case impl(arg_vals) {
            Some(result) -> result
            None -> VCall(name, arg_vals)
          }
        }
        Error(Nil) -> VCall(name, arg_vals)
      }
    }
    Comptime(term) -> eval(ffi, env, term)
    Fix(name, body) -> VFix(name, env, body)
    Err(_) -> VErr
    // Error terms evaluate to VErr
  }
}

/// Evaluate a field projection.
///
/// If the value is neutral (unknown), the projection is added to the spine.
/// If the value is a record, the field is looked up immediately.
fn do_dot(value: Value, name: String) -> Value {
  case value {
    VNeut(head, spine) -> VNeut(head, [EDot(name), ..spine])
    VRcd(fields) ->
      case list.key_find(fields, name) {
        Ok(v) -> v
        Error(Nil) -> VErr
      }
    _ -> VErr
  }
}

/// Apply a function to an argument.
///
/// If the function is neutral (unknown), the application is added to the spine.
/// If the function is a lambda, the argument is substituted into the body.
/// If the function is a fixpoint, it unfolds by substituting itself into its body.
/// Otherwise, returns VErr (not a function).
pub fn do_app(ffi: FFI, fun: Value, arg: Value) -> Value {
  case fun {
    VNeut(head, spine) -> VNeut(head, [EApp(arg), ..spine])
    VLam(_, _, env, body) -> eval(ffi, [arg, ..env], body)
    VFix(name, env, body) -> {
      // Unfold fixpoint: substitute the fixpoint itself for the name in the body
      // Then apply to the argument
      let fix_val = VFix(name, env, body)
      let lam_val = VLam([], name, [fix_val, ..env], body)
      do_app(ffi, lam_val, arg)
    }
    _ -> VErr
  }
}

/// Apply a function with an implicit type argument.
///
/// The implicit argument is evaluated but erased at runtime.
/// For neutral terms, the implicit application is added to the spine.
fn do_app_implicit(fun: Value, implicit_val: Value) -> Value {
  case fun {
    VNeut(head, spine) -> VNeut(head, [EAppImplicit(implicit_val), ..spine])
    VLam(implicit_params, name, env, body) -> {
      // Implicit arg is erased - just continue with the lambda
      // The type info is used at type-checking time, not runtime
      VLam(list.drop(implicit_params, 1), name, env, body)
    }
    _ -> fun
  }
}

/// Apply a function with a list of implicit arguments, then an explicit argument.
///
/// This recursively handles implicit args until the base case (empty list).
fn do_app_with_implicit(ffi: FFI, fun: Value, implicit: List(Term), arg: Value) -> Value {
  case implicit {
    [] -> do_app(ffi, fun, arg)
    [implicit_arg, ..rest] -> {
      // This shouldn't happen in normal evaluation - implicit args should be
      // handled during the initial App evaluation
      // But handle it recursively just in case
      let implicit_val = eval(ffi, [], implicit_arg)
      let instantiated = do_app_implicit(fun, implicit_val)
      do_app_with_implicit(ffi, instantiated, rest, arg)
    }
  }
}

/// Evaluate a pattern match.
///
/// If the argument is neutral (unknown), the match is delayed by adding it to
/// the spine. Otherwise, we try to match the argument against each case.
///
/// The motive is the return type of the match (for dependent pattern matching).
pub fn do_match(env: Env, arg: Value, motive: Value, cases: List(Case)) -> Value {
  case arg {
    VNeut(head, spine) -> VNeut(head, [EMatch(env, motive, cases), ..spine])
    _ ->
      case do_match_cases(arg, cases) {
        Some(#(bindings, body)) -> eval([], list.append(bindings, env), body)
        None -> VErr
      }
  }
}

/// Try to match a value against a list of cases, returning the first match.
///
/// Returns the bindings (environment) and body of the matching case.
pub fn do_match_cases(arg: Value, cases: List(Case)) -> Option(#(Env, Term)) {
  case cases {
    [] -> None
    [c, ..cases] ->
      case do_match_pattern(c.pattern, arg) {
        Ok(env) -> {
          // Check guard if present
          case c.guard {
            Some(guard_term) -> {
              // Evaluate guard in the extended environment
              let guard_val = eval([], env, guard_term)
              // For now, treat any non-error guard value as true
              // (proper boolean checking would be better)
              case guard_val {
                VErr -> do_match_cases(arg, cases)
                _ -> Some(#(env, c.body))
              }
            }
            None -> Some(#(env, c.body))
          }
        }
        Error(Nil) -> do_match_cases(arg, cases)
      }
  }
}

/// Match a pattern against a value, returning bindings on success.
///
/// This is runtime pattern matching (used during evaluation), not type checking.
/// PAny always matches. PAs binds the matched value. Constructors and records
/// recursively match their contents.
pub fn do_match_pattern(pattern: Pattern, value: Value) -> Result(Env, Nil) {
  case pattern, value {
    PAny, _ -> Ok([])
    PAs(p, _), _ -> {
      use env <- result.try(do_match_pattern(p, value))
      // PAs binds the matched value (for use in the body)
      Ok(list.append(env, [value]))
    }
    PTyp(pk), VTyp(vk) if pk == vk -> Ok([])
    PLit(pk), VLit(vk) if pk == vk -> Ok([])
    PLitT(pk), VLitT(vk) if pk == vk -> Ok([])
    PRcd(pfields), VRcd(vfields) ->
      list.try_fold(pfields, [], fn(acc_env, pfield) {
        let #(name, p) = pfield
        use v <- result.try(list.key_find(vfields, name))
        use env <- result.try(do_match_pattern(p, v))
        Ok(list.append(acc_env, env))
      })
    PCtr(ptag, parg), VCtr(vtag, varg) if ptag == vtag ->
      do_match_pattern(parg, varg)
    _, _ -> Error(Nil)
  }
}

// ============================================================================
// NORMALIZATION BY EVALUATION
// ============================================================================
// Normalization by Evaluation (NbE) works by:
// 1. Evaluating a term to its semantic value (normal form)
// 2. Quoting the value back to syntax
//
// This is more efficient than syntactic reduction and handles alpha-equivalence
// automatically (since bound variables are represented canonically).

/// Normalize a term by evaluating and quoting back to syntax.
///
/// This produces the beta-normal, eta-long form of the term.
pub fn normalize(ffi: FFI, env: Env, term: Term, s: Span) -> Term {
  let val = eval(ffi, env, term)
  quote(ffi, list.length(env), val, s)
}

/// Quote a value back to syntax (reification).
///
/// The level parameter tracks the current De Bruijn level. When quoting a
/// lambda, we create a fresh neutral variable at the current level, apply it
/// to the body, and quote the result. This converts De Bruijn levels back to
/// indices using the formula: index = lvl - level - 1.
pub fn quote(ffi: FFI, lvl: Int, value: Value, s: Span) -> Term {
  case value {
    VTyp(k) -> Term(Typ(k), s)
    VLit(k) -> Term(Lit(k), s)
    VLitT(k) -> Term(LitT(k), s)
    VNeut(head, spine) -> {
      let head_term = quote_head(lvl, head, s)
      quote_neut(ffi, lvl, head_term, spine, s)
    }
    VRcd(fields) ->
      Term(
        Rcd(list.map(fields, fn(kv) { #(kv.0, quote(ffi, lvl, kv.1, s)) })),
        s,
      )
    VCtr(tag, arg) -> Term(Ctr(tag, quote(ffi, lvl, arg, s)), s)
    VLam(implicit, name, env, body) -> {
      // Create a fresh neutral variable at the current level
      let fresh = VNeut(HVar(lvl), [])
      // Apply it to the body and evaluate
      let body_val = eval(ffi, [fresh, ..env], body)
      // Quote the result at level + 1
      let body_quote = quote(ffi, lvl + 1, body_val, body.span)
      Term(Lam(implicit, #(name, Term(Hole(-1), s)), body_quote), s)
    }
    VPi(implicit, name, env, in_val, out_term) -> {
      // Quote the domain (already evaluated)
      let in_quote = quote(ffi, lvl, in_val, s)
      // Create a fresh neutral variable for the codomain
      let fresh = VNeut(HVar(lvl), [])
      let out_val = eval(ffi, [fresh, ..env], out_term)
      let out_quote = quote(ffi, lvl + 1, out_val, out_term.span)
      Term(Pi(implicit, name, in_quote, out_quote), s)
    }
    VRecord(fields) -> {
      // Record type - quote each field type
      Term(
        Rcd(list.map(fields, fn(kv) { #(kv.0, quote(ffi, lvl, kv.1, s)) })),
        s,
      )
    }
    VCall(name, args) -> {
      // Quote stuck built-in with collected args
      Term(Call(name, list.map(args, fn(a) { quote(ffi, lvl, a, s) })), s)
    }
    VFix(name, env, body) -> {
      // Quote fixpoint: create a fresh variable and quote the body
      let fresh = VNeut(HVar(lvl), [])
      let body_val = eval(ffi, [fresh, ..env], body)
      let body_quote = quote(ffi, lvl + 1, body_val, body.span)
      Term(Fix(name, body_quote), s)
    }
    VErr -> Term(Hole(-1), s)
  }
}

/// Quote a neutral term by reconstructing the head and applying the spine.
fn quote_neut(
  ffi: FFI,
  lvl: Int,
  head: Term,
  spine: List(Elim),
  s: Span,
) -> Term {
  list.fold_right(spine, head, fn(head, elim) {
    quote_elim(ffi, lvl, head, elim, s)
  })
}

/// Quote a single elimination (spine element).
fn quote_elim(ffi: FFI, lvl: Int, head: Term, elim: Elim, s: Span) -> Term {
  case elim {
    EDot(name) -> Term(Dot(head, name), s)
    EApp(arg) -> Term(App(head, [], quote(ffi, lvl, arg, s)), s)
    EAppImplicit(implicit_val) -> {
      // Implicit application - add to implicit list
      // For now, just quote the implicit value
      // This creates a term like: head<implicit_val>()
      // We need to handle this specially
      Term(App(head, [quote(ffi, lvl, implicit_val, s)], Term(Hole(-1), s)), s)
    }
    // The env is discarded because we're reconstructing syntax, not evaluating.
    // The cases bodies are already Terms (syntax), not Values, so they don't
    // need quoting. The env was only needed during evaluation to capture the
    // closure environment for delayed matching on neutral terms.
    EMatch(_, motive, cases) ->
      Term(Match(head, quote(ffi, lvl, motive, s), cases), s)
  }
}

/// Quote a neutral head (variable or hole) back to a term.
///
/// For variables, converts from De Bruijn level to index:
/// index = lvl - level - 1
///
/// For example, at level 5, quoting HVar(2):
/// index = 5 - 2 - 1 = 2
fn quote_head(lvl: Int, head: Head, s: Span) -> Term {
  case head {
    HVar(l) -> Term(Var(lvl - l - 1), s)
    HHole(id) -> Term(Hole(id), s)
  }
}

// ============================================================================
// UNIFICATION
// ============================================================================
// Unification solves metavariables by comparing two values and accumulating
// solutions in the substitution. It implements higher-order unification with
// an occurs check to prevent infinite types.

/// Check if a value contains a specific hole (occurs check).
///
/// This prevents infinite types like ?0 = ?0 → ?0 by checking if the hole
/// being solved appears in the solution. The substitution is forced to
/// check through solved metavariables.
pub fn occurs(sub: Subst, id: Int, value: Value) -> Bool {
  case force([], sub, value) {
    VTyp(_) | VLit(_) | VLitT(_) | VErr -> False
    VNeut(HHole(hole_id), spine) ->
      id == hole_id || list.any(spine, occurs_elim(sub, id, _))
    VNeut(_, spine) -> list.any(spine, occurs_elim(sub, id, _))
    VRcd(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
    VCtr(_, arg) -> occurs(sub, id, arg)
    VLam(_, _, env, _) -> list.any(env, occurs(sub, id, _))
    VPi(_, _, env, in, _) ->
      occurs(sub, id, in) || list.any(env, occurs(sub, id, _))
    VCall(_, args) -> list.any(args, occurs(sub, id, _))
    VFix(_, env, _) -> list.any(env, occurs(sub, id, _))
    VRecord(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
  }
}

/// Check if an elimination (spine element) contains a specific hole.
pub fn occurs_elim(sub: Subst, id: Int, elim: Elim) -> Bool {
  case elim {
    EDot(_) -> False
    EApp(arg) -> occurs(sub, id, arg)
    EAppImplicit(arg) -> occurs(sub, id, arg)
    EMatch(env, motive, _) ->
      occurs(sub, id, motive) || list.any(env, occurs(sub, id, _))
  }
}

/// Unify two values, solving metavariables and accumulating solutions.
///
/// Returns Ok(state) with updated substitution if unification succeeds.
/// Returns Error if the values are incompatible (type error).
///
/// IMPORTANT: `unify` itself is NOT error-resilient—it returns errors
/// immediately when values don't match. Error recovery happens at the
/// `infer` and `check` level, which catch unify errors, record them in
/// the state, and continue with VErr.
///
/// Key cases:
/// - Holes: If one side is an unsolved hole, solve it (with occurs check)
/// - Neutral terms: Unify heads and spines (errors on mismatch)
/// - Lambdas/Pis: Create fresh variable, apply to both, unify results
/// - VErr: Always succeeds (propagates errors without blocking)
pub fn unify(
  s: State,
  v1: Value,
  v2: Value,
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case v1, v2 {
    VTyp(k1), VTyp(k2) if k1 == k2 -> Ok(s)
    VLit(k1), VLit(k2) if k1 == k2 -> Ok(s)
    VLitT(k1), VLitT(k2) if k1 == k2 -> Ok(s)
    VNeut(HHole(id), []), _ ->
      case list.key_find(s.sub, id) {
        Ok(v) -> unify(s, v, v2, s1, s2)
        Error(Nil) ->
          case occurs(s.sub, id, v2) {
            True -> Error(InfiniteType(id, v2, s1, s2))
            False -> Ok(State(..s, sub: [#(id, v2), ..s.sub]))
          }
      }
    _, VNeut(HHole(_), []) -> unify(s, v2, v1, s2, s1)
    VNeut(h1, spine1), VNeut(h2, spine2) if h1 == h2 ->
      unify_elim_list(s, spine1, spine2, s1, s2)
    VRcd(fields1), VRcd(fields2) -> unify_fields(s, fields1, fields2, s1, s2)
    VCtr(k1, arg1), VCtr(k2, arg2) if k1 == k2 -> unify(s, arg1, arg2, s1, s2)
    VLam(_, _, env1, body1), VLam(_, _, env2, body2) -> {
      // Unify lambdas by applying both to a fresh variable
      let #(fresh, s) = new_var(s)
      let a = eval(s.ffi, [fresh, ..env1], body1)
      let b = eval(s.ffi, [fresh, ..env2], body2)
      unify(s, a, b, s1, s2)
    }
    VPi(implicit1, _, env1, in1, out1), VPi(implicit2, _, env2, in2, out2) -> {
      // First check implicit params match
      case implicit1 == implicit2 {
        False -> Error(TypeMismatch(VPi(implicit1, "", [], in1, out1), VPi(implicit2, "", [], in2, out2), s1, s2))
        True -> {
          // Unify Pi types: first domains, then codomains
          use _ <- result.try(unify(s, in1, in2, s1, s2))
          let #(fresh, s) = new_var(s)
          let a = eval(s.ffi, [fresh, ..env1], out1)
          let b = eval(s.ffi, [fresh, ..env2], out2)
          unify(s, a, b, s1, s2)
        }
      }
    }
    VErr, _ -> Ok(s)
    _, VErr -> Ok(s)
    _, _ -> Error(TypeMismatch(v1, v2, s1, s2))
  }
}

/// Unify two record field lists.
///
/// Records are compared by field name (order doesn't matter). Missing fields
/// produce an error. Fields are sorted by name during comparison.
fn unify_fields(
  s: State,
  args1: List(#(String, Value)),
  args2: List(#(String, Value)),
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case args1 {
    [] ->
      case list.map(args2, fn(kv) { kv.0 }) {
        [] -> Ok(s)
        names -> Error(RcdMissingFields(names, s1))
      }
    [#(name, v1), ..args1] ->
      case list.key_pop(args2, name) {
        Error(Nil) -> {
          let names =
            list.filter(args1, fn(kv) {
              list.key_find(args2, kv.0) == Error(Nil)
            })
            |> list.map(fn(kv) { kv.0 })
          Error(RcdMissingFields([name, ..names], s2))
        }
        Ok(#(v2, args2)) -> {
          use s <- result.try(unify(s, v1, v2, s1, s2))
          unify_fields(s, args1, args2, s1, s2)
        }
      }
  }
}

/// Unify two eliminations (spine elements).
///
/// Returns an error if the eliminations are incompatible (e.g., projection
/// vs. application). This error will be caught by the caller and recorded
/// for error recovery.
fn unify_elim(
  s: State,
  e1: Elim,
  e2: Elim,
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case e1, e2 {
    EDot(n1), EDot(n2) if n1 == n2 -> Ok(s)
    EApp(a1), EApp(a2) -> unify(s, a1, a2, s1, s2)
    // Spine mismatch: incompatible eliminations
    // Return error - caller will record it and continue with VErr
    _, _ -> Error(SpineMismatch(s1, s2))
  }
}

/// Unify two spine lists element-by-element.
///
/// Returns an error if the spines have different lengths or incompatible
/// elements. This error will be caught by the caller and recorded for
/// error recovery.
fn unify_elim_list(
  s: State,
  l1: List(Elim),
  l2: List(Elim),
  s1: Span,
  s2: Span,
) -> Result(State, Error) {
  case l1, l2 {
    [], [] -> Ok(s)
    [e1, ..xs], [e2, ..ys] -> {
      use s <- result.try(unify_elim(s, e1, e2, s1, s2))
      unify_elim_list(s, xs, ys, s1, s2)
    }
    // Arity mismatch: different number of eliminations
    // Return error - caller will record it and continue with VErr
    [], _ | _, [] -> Error(ArityMismatch(s1, s2))
  }
}

/// Add an error to the state's error list.
///
/// Used throughout type checking to accumulate errors rather than failing
/// immediately. This enables IDE support where all errors are shown at once.
pub fn with_err(s: State, err: Error) -> State {
  State(..s, errors: list.append(s.errors, [err]))
}

// ============================================================================
// BIDIRECTIONAL TYPE CHECKING
// ============================================================================
// Bidirectional typing uses two modes:
//
// 1. INFER (synthesis): Given a term, compute its type
//    - Used for: variables, literals, applications, holes
//    - Direction: term → type (bottom-up)
//
// 2. CHECK (verification): Given a term and expected type, verify it matches
//    - Used for: lambdas, constructors, annotations
//    - Direction: type → term (top-down)
//
// This allows omitting type annotations where inference is possible.
//
// ERROR RECOVERY DESIGN:
// - `unify` returns errors immediately when types don't match
// - `infer` and `check` catch these errors, record them via `with_err`,
//   and continue with `VErr` values
// - This ensures all errors are reported in one pass (critical for LSP/IDE)
// - The guarantee: if there are no errors, the program is fully correct

/// Infer the type of a term (synthesis direction).
///
/// Returns the evaluated value, its type, and the updated state.
///
/// ERROR HANDLING: On error, records the error in state and returns VErr
/// for both value and type, allowing checking to continue.
///
/// Key cases:
/// - Variables: Look up in context
/// - Applications: Infer function type, check argument, return result type
/// - Lambdas: Create a hole for the domain, infer the codomain
/// - Constructors: Look up definition, solve GADT parameters via unification
/// - Match: Infer scrutinee type, check motive, verify exhaustiveness
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term.data {
    Typ(k) -> #(VTyp(k), VTyp(k + 1), s)
    Lit(k) -> #(VLit(k), typeof_lit(k), s)
    LitT(k) -> #(VLitT(k), VTyp(0), s)
    Var(i) ->
      case ctx_get(s.ctx, i) {
        Some(#(val, ty)) -> #(val, ty, s)
        None -> infer_error(s, VarUndefined(i, term.span))
      }
    Hole(id) -> {
      // Record unsolved hole as a warning for IDE feedback
      let #(ty, s) = new_hole(s)
      #(VNeut(HHole(id), []), ty, with_err(s, HoleUnsolved(id, term.span)))
    }
    Rcd(fields) -> {
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #(VRcd(fields_val), VRcd(fields_ty), s)
    }
    Ctr(tag, arg) ->
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> infer_error(s, CtrUndefined(tag, term.span))
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, _, s) = check_ctr_def(s, ctr)
          let #(_, arg_ty, s) = infer(s, arg)
          let #(_, s) =
            check_type(s, arg_ty, ctr_arg_ty, arg.span, ctr.arg_ty.span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, term.span)
          let env = list.append(params, get_env(s))
          #(VCtr(tag, eval(s.ffi, env, arg)), eval(s.ffi, env, ctr.ret_ty), s)
        }
      }
    Dot(arg, name) -> {
      let #(arg_val, arg_ty, s) = infer(s, arg)
      let val = do_dot(arg_val, name)
      case arg_ty {
        VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> #(val, ty, s)
            Error(Nil) -> {
              let s = with_err(s, DotFieldNotFound(name, fields, arg.span))
              #(val, VErr, s)
            }
          }
        _ -> #(val, VErr, with_err(s, DotOnNonCtr(arg_ty, name, arg.span)))
      }
    }
    Ann(term, term_ty) -> {
      let #(ty_val, _, s) = infer(s, term_ty)
      let #(val, s) = check(s, term, ty_val, term_ty.span)
      #(val, ty_val, s)
    }
    Lam(implicit, param, body) -> {
      // For lambda inference, we create a hole for the domain type
      let #(name, _) = param
      let env = get_env(s)
      let #(t1_hole, s) = new_hole(s)
      let #(_fresh, s) = def_var(s, name, t1_hole)
      let #(body_val, body_ty, s) = infer(s, body)
      // Quote the body back to preserve structure even if there are errors
      let body_quoted = quote(s.ffi, list.length(env), body_val, body.span)
      let t1 = force(s.ffi, s.sub, t1_hole)
      let t2 = quote(s.ffi, list.length(env), body_ty, body.span)
      #(VLam(implicit, name, env, body_quoted), VPi(implicit, name, env, t1, t2), s)
    }
    Pi(implicit, name, in_term, out_term) -> {
      let env = get_env(s)
      let #(in_val, _, s) = infer(s, in_term)
      let #(_, s) = def_var(s, name, in_val)
      let #(_, _, s) = infer(s, out_term)
      #(VPi(implicit, name, env, in_val, out_term), VTyp(0), s)
    }
    App(fun, implicit, arg) -> {
      let #(fun_val, fun_ty, s) = infer(s, fun)
      case fun_ty {
        VPi(_, _, pi_env, in, out) -> {
          let #(arg_val, s) = check(s, arg, in, fun.span)
          let out_val = eval(s.ffi, [arg_val, ..pi_env], out)
          #(do_app(s.ffi, fun_val, arg_val), out_val, s)
        }
        VNeut(HHole(hole_id), []) -> {
          // Hole expansion: ?1 applied to arg means ?1 = (?2 -> ?3)
          let env = get_env(s)
          let #(arg_ty_hole_val, s) = new_hole(s)
          let result_ty_hole_id = s.hole
          let #(result_ty_hole_val, s) = new_hole(s)
          // Create the expanded function type: (?2 -> ?3)
          let fun_ty_expanded =
            VPi(
              [],
              "_",
              env,
              arg_ty_hole_val,
              Term(Hole(result_ty_hole_id), fun.span),
            )
          // Unify the original hole with the expanded type
          case
            unify(
              s,
              VNeut(HHole(hole_id), []),
              fun_ty_expanded,
              fun.span,
              fun.span,
            )
          {
            Ok(s) -> {
              // Now check the argument against the domain hole
              let #(arg_val, s) = check(s, arg, arg_ty_hole_val, arg.span)
              // Result type is the codomain hole (as a value)
              let out_val = result_ty_hole_val
              #(do_app(s.ffi, fun_val, arg_val), out_val, s)
            }
            Error(_) -> #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
          }
        }
        _ -> #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
      }
    }
    Match(arg, motive, cases) -> {
      let env = get_env(s)
      let #(arg_val, arg_ty, s) = infer(s, arg)
      // The motive type is (x : arg_ty) → Type, where x is the scrutinee
      let motive_ty = VPi([], "_", env, arg_ty, Term(Typ(0), arg.span))
      let #(motive_val, s) = check(s, motive, motive_ty, motive.span)
      let s =
        list.fold(cases, s, fn(s, c) {
          let #(pat_val, s) =
            bind_pattern(s, c.pattern, arg_ty, c.span, arg.span)
          let branch_ty = do_app(s.ffi, motive_val, pat_val)
          // Check guard if present (must be boolean-ish)
          let s = case c.guard {
            Some(guard_term) -> {
              let #(_guard_val, _guard_ty, s) = infer(s, guard_term)
              s
            }
            None -> s
          }
          let #(_, s) = check(s, c.body, branch_ty, c.span)
          s
        })
      // Run exhaustiveness checking and add any errors to the state
      let exhaustiveness_errors = check_exhaustiveness(s, cases, term.span)
      let s = list.fold(exhaustiveness_errors, s, with_err)
      let match_val = do_match(env, arg_val, motive_val, cases)
      let result_ty = do_app(s.ffi, motive_val, arg_val)
      #(match_val, result_ty, s)
    }
    Call(name, args) -> {
      // Look up built-in in host registry
      case list.key_find(s.ffi, name) {
        Ok(Builtin(impl, _)) -> {
          // Evaluate arguments
          let #(arg_vals, arg_tys, s1) = infer_args(s, args)

          // Execute built-in (pure function) - returns None for non-concrete args
          case impl(arg_vals) {
            Some(result_val) -> {
              // Compute result type (simplified - assumes all args have same type)
              let result_ty = case arg_tys {
                [ty, ..] -> ty
                [] -> VErr
              }
              #(result_val, result_ty, s1)
            }
            None -> {
              // Arguments not concrete - defer to runtime
              let result_ty = case arg_tys {
                [ty, ..] -> ty
                [] -> VErr
              }
              #(VCall(name, arg_vals), result_ty, s1)
            }
          }
        }
        Error(Nil) -> {
          // Unknown built-in - return VCall (deferred to runtime)
          let #(arg_vals, arg_tys, s1) = infer_args(s, args)
          let result_ty = case arg_tys {
            [ty, ..] -> ty
            [] -> VErr
          }
          #(VCall(name, arg_vals), result_ty, s1)
        }
      }
    }
    Comptime(term) -> {
      // Comptime blocks are evaluated during elaboration
      // Execute with comptime_eval for permission checking
      let #(val, s1) = comptime_eval(s, term)
      // Quote the result back to a term and infer its type
      let quoted = quote(s1.ffi, 0, val, term.span)
      let #(val2, ty, s2) = infer(s1, quoted)
      #(val2, ty, s2)
    }
    Fix(name, body) -> {
      // Fixpoint: fix f -> body has type A if body : A -> A
      // We create a hole for the result type and check that body has type hole -> hole
      let env = get_env(s)
      let #(result_ty_hole, s) = new_hole(s)
      // The function type is result_ty -> result_ty
      let fun_ty =
        VPi([], name, env, result_ty_hole, Term(Hole(s.hole - 1), body.span))
      // Add the fixpoint variable to the context with the function type
      let #(_fresh, s) = def_var(s, name, fun_ty)
      let #(_body_val, s) = check(s, body, result_ty_hole, body.span)
      // Return the fixpoint value with the result type
      let fix_val = VFix(name, env, body)
      #(fix_val, result_ty_hole, s)
    }
    Err(_) -> #(VErr, VErr, s)
    // Error terms have error type
  }
}

/// Infer types for all arguments
fn infer_args(s: State, args: List(Term)) -> #(List(Value), List(Type), State) {
  infer_args_loop(args, [], [], s)
}

fn infer_args_loop(
  args: List(Term),
  vals: List(Value),
  tys: List(Type),
  s: State,
) -> #(List(Value), List(Type), State) {
  case args {
    [] -> #(list.reverse(vals), list.reverse(tys), s)
    [arg, ..rest] -> {
      let #(val, ty, s1) = infer(s, arg)
      infer_args_loop(rest, [val, ..vals], [ty, ..tys], s1)
    }
  }
}

/// Get the type of a literal value.
fn typeof_lit(lit: Literal) -> Value {
  case lit {
    I32(_) -> VLitT(I32T)
    I64(_) -> VLitT(I64T)
    U32(_) -> VLitT(U32T)
    U64(_) -> VLitT(U64T)
    F32(_) -> VLitT(F32T)
    F64(_) -> VLitT(F64T)
  }
}

/// Infer types for all record fields.
fn infer_fields(
  s: State,
  fields: List(#(String, Term)),
) -> #(List(#(String, Value)), List(#(String, Type)), State) {
  case fields {
    [] -> #([], [], s)
    [#(name, term), ..fields] -> {
      let #(val, ty, s) = infer(s, term)
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #([#(name, val), ..fields_val], [#(name, ty), ..fields_ty], s)
    }
  }
}

/// Bind variables from a pattern against an expected type.
///
/// This is used during type checking of match branches and let-bindings.
/// It adds bound variables to the context and returns the matched value.
///
/// Key cases:
/// - PAny: Creates a hole (unknown value)
/// - PAs: Binds the matched value with the given name
/// - PRcd: Recursively binds fields, reporting missing ones
/// - PCtr: Solves GADT parameters via unification with the expected type
pub fn bind_pattern(
  s: State,
  pattern: Pattern,
  ret_ty: Value,
  pat_span: Span,
  ret_span: Span,
) -> #(Value, State) {
  case pattern {
    PAny -> new_hole(s)
    PAs(PAny, name) -> def_var(s, name, ret_ty)
    PAs(p, name) -> {
      let #(_, s) = def_var(s, name, ret_ty)
      bind_pattern(s, p, ret_ty, pat_span, ret_span)
    }
    PTyp(k) -> check(s, Term(Typ(k), pat_span), ret_ty, ret_span)
    PLit(k) -> check(s, Term(Lit(k), pat_span), ret_ty, ret_span)
    PLitT(k) -> check(s, Term(LitT(k), pat_span), ret_ty, ret_span)
    PRcd(pfields) ->
      case ret_ty {
        VRcd(vfields) -> {
          let missing =
            list.filter_map(pfields, fn(kv) {
              case list.key_find(vfields, kv.0) {
                Error(Nil) -> Ok(kv.0)
                Ok(_) -> Error(Nil)
              }
            })
          let s = case missing {
            [] -> s
            _ -> with_err(s, RcdMissingFields(missing, ret_span))
          }
          let #(fields, s) =
            list.fold_right(pfields, #([], s), fn(acc, kv) {
              let #(fields, s) = acc
              let #(name, p) = kv
              let #(ty, s) = case list.key_find(vfields, name) {
                Error(Nil) -> new_hole(s)
                Ok(ty) -> #(ty, s)
              }
              let #(v, s) = bind_pattern(s, p, ty, pat_span, ret_span)
              #([#(name, v), ..fields], s)
            })
          #(VRcd(fields), s)
        }
        _ -> #(
          VErr,
          with_err(s, PatternMismatch(pattern, ret_ty, pat_span, ret_span)),
        )
      }
    PCtr(tag, parg) -> {
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> #(VErr, with_err(s, CtrUndefined(tag, pat_span)))
        Ok(ctr) -> {
          let #(params, _, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, s) =
            check_type(s, ctr_ret_ty, ret_ty, ctr.ret_ty.span, ret_span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, pat_span)
          let env = list.append(params, get_env(s))
          let ctr_arg_ty = eval(s.ffi, env, ctr.arg_ty)
          let #(varg, s) =
            bind_pattern(s, parg, ctr_arg_ty, pat_span, ctr.arg_ty.span)
          #(VCtr(tag, varg), s)
        }
      }
    }
  }
}

/// Check that a term has the expected type (verification direction).
///
/// Returns the evaluated value and updated state.
///
/// ERROR HANDLING: On error, records the error in state and returns VErr,
/// allowing checking to continue. This is how error recovery is implemented.
///
/// Note: This function now delegates entirely to infer + unify. The bidirectional
/// structure is kept for API clarity and future extensions, but currently all
/// terms follow the same infer-then-unify pattern.
pub fn check(
  s: State,
  term: Term,
  expected_ty: Type,
  ty_span: Span,
) -> #(Value, State) {
  let #(value, inferred_ty, s) = infer(s, term)
  case unify(s, inferred_ty, expected_ty, term.span, ty_span) {
    Ok(s) -> #(force(s.ffi, s.sub, value), s)
    Error(e) -> #(VErr, with_err(s, e))
  }
}

/// Process a constructor definition for type checking.
///
/// Creates holes for each type parameter and infers the argument and
/// return types in the extended context. Returns the parameter hole IDs
/// and the inferred types.
fn check_ctr_def(s: State, ctr: CtrDef) -> #(List(Int), Value, Value, State) {
  let #(params, s) =
    list.fold(ctr.params, #([], s), fn(acc, name) {
      let #(params, s) = acc
      let id = s.hole
      let #(hole, s) = new_hole(s)
      let params = [id, ..params]
      let s = State(..s, ctx: [#(name, #(hole, VTyp(0))), ..s.ctx])
      #(params, s)
    })
  let #(arg_ty, _, s) = infer(s, ctr.arg_ty)
  let #(ret_ty, _, s) = infer(s, ctr.ret_ty)
  #(params, arg_ty, ret_ty, s)
}

/// Check that two types are equal by unifying them.
///
/// Returns the forced (substituted) type and updated state.
///
/// ERROR HANDLING: On unify failure, records the error and returns.
/// This is the primary place where unify errors are caught and converted
/// to error recovery (VErr propagation).
pub fn check_type(
  s: State,
  t1: Value,
  t2: Value,
  t1_span: Span,
  t2_span: Span,
) -> #(Value, State) {
  case unify(s, t1, t2, t1_span, t2_span) {
    Ok(s) -> #(force(s.ffi, s.sub, t1), s)
    Error(e) -> #(t1, with_err(s, e))
  }
}

/// Force all solved metavariables in a value.
///
/// This recursively replaces holes with their solutions from the
/// substitution. If a hole has a spine (pending operations), the
/// spine is applied to the solution.
pub fn force(ffi: FFI, sub: Subst, value: Value) -> Value {
  case value {
    VNeut(HHole(id), spine) ->
      case list.key_find(sub, id) {
        Ok(v) -> {
          let forced_val = apply_spine(ffi, v, spine)
          force(ffi, sub, forced_val)
        }
        Error(Nil) -> value
      }
    _ -> value
  }
}

/// Apply a spine (list of eliminations) to a value.
///
/// This is used when forcing metavariables that have pending operations.
fn apply_spine(ffi: FFI, value: Value, spine: List(Elim)) -> Value {
  list.fold(spine, value, fn(value, elim) {
    case elim {
      EDot(field) -> do_dot(value, field)
      EApp(arg) -> do_app(ffi, value, arg)
      EAppImplicit(_) -> value  // Implicit args are erased at runtime
      EMatch(env, motive, cases) -> do_match(env, value, motive, cases)
    }
  })
}

/// Solve constructor parameters from the substitution.
///
/// After unifying a constructor's return type with the expected type,
/// the parameters should be solved. This function extracts them from
/// the substitution, recording errors for any unsolved parameters.
pub fn ctr_solve_params(
  s: State,
  ctr: CtrDef,
  params: List(Int),
  tag: String,
  span: Span,
) -> #(Env, State) {
  list.fold(params, #([], s), fn(acc, id) {
    let #(acc_params, s) = acc
    case list.key_find(s.sub, id) {
      Ok(val) -> #(list.append(acc_params, [val]), s)
      Error(Nil) -> #(
        list.append(acc_params, [VNeut(HHole(id), [])]),
        with_err(s, CtrUnsolvedParam(tag, ctr, id, span)),
      )
    }
  })
}

// ============================================================================
// EXHAUSTIVENESS CHECKING
// ============================================================================
// Implementation of Maranget's algorithm for pattern match exhaustiveness.
// Reference: http://moscova.inria.fr/~maranget/papers/warn/index.html
//
// The algorithm uses a matrix where:
// - Each row is a pattern already matched
// - We check if a new pattern (vector) is "useful" (covers new cases)
// - If useful, it's not redundant
// - If the matrix doesn't cover all cases, we get missing witnesses

/// Deconstruct a pattern into its head constructor and arguments.
///
/// The head determines which specializations are possible.
/// For records, fields are sorted by name for canonical comparison.
fn deconstruct(pat: Pattern) -> #(PHead, List(Pattern)) {
  case pat {
    PAny -> #(HAny, [])
    PAs(p, _) -> deconstruct(p)
    PTyp(k) -> #(HTyp(k), [])
    PLit(k) -> #(HLit(k), [])
    PLitT(k) -> #(HLitT(k), [])
    PRcd(fields) -> {
      let sorted = list.sort(fields, fn(a, b) { string.compare(a.0, b.0) })
      let head = HRcd(list.map(sorted, fn(f) { f.0 }))
      #(head, list.map(sorted, fn(f) { f.1 }))
    }
    PCtr(tag, p) -> #(HCtr(tag), [p])
  }
}

/// Reconstruct a pattern from its head and arguments.
fn reconstruct(head: PHead, args: List(Pattern)) -> Pattern {
  case head {
    HAny -> PAny
    HTyp(k) -> PTyp(k)
    HLit(k) -> PLit(k)
    HLitT(k) -> PLitT(k)
    HRcd(ks) -> PRcd(list.zip(ks, args))
    HCtr(tag) -> PCtr(tag, list.first(args) |> result.unwrap(PAny))
  }
}

/// Get the arity (number of arguments) of a pattern head.
fn head_arity(head: PHead) -> Int {
  case head {
    HRcd(fs) -> list.length(fs)
    HCtr(_) -> 1
    _ -> 0
  }
}

/// Compute the default matrix by removing patterns that aren't wildcards.
///
/// Used when the first pattern is a wildcard—we skip it and continue
/// with the rest of the row.
fn default_matrix(matrix: PMatrix) -> PMatrix {
  list.filter_map(matrix, fn(row) {
    case row {
      [first, ..rest] -> {
        case deconstruct(first).0 {
          HAny -> Ok(rest)
          _ -> Error(Nil)
        }
      }
      [] -> Error(Nil)
    }
  })
}

/// Specialize a matrix for a specific constructor head.
///
/// For each row:
/// - If the first pattern matches the target, extract its arguments
/// - If the first pattern is a wildcard, expand it with wildcards
/// - Otherwise, the row doesn't apply
pub fn specialize(matrix: PMatrix, target: PHead) -> PMatrix {
  list.filter_map(matrix, fn(row) {
    case row {
      [p, ..ps] -> {
        case deconstruct(p) {
          #(head, args) if head == target -> Ok(list.append(args, ps))
          #(HAny, _) -> {
            // Wildcard expands to match any constructor
            let qs = list.repeat(PAny, head_arity(target))
            Ok(list.append(qs, ps))
          }
          _ -> Error(Nil)
        }
      }
      _ -> Error(Nil)
    }
  })
}

/// Extract all concrete (non-wildcard) heads from the first column.
///
/// Used to determine which constructors are already covered.
pub fn get_concrete_heads(matrix: PMatrix) -> List(PHead) {
  list.filter_map(matrix, fn(r) {
    case r {
      [p, ..] ->
        case deconstruct(p).0 {
          HAny -> Error(Nil)
          h -> Ok(h)
        }
      _ -> Error(Nil)
    }
  })
  |> list.unique
}

/// Find missing constructor heads for GADT-style exhaustiveness.
///
/// For constructor patterns, we check which other constructors of the
/// same type could apply but aren't covered. This handles GADTs where
/// different constructors may have different return types.
pub fn get_missing_heads(
  s: State,
  index: CtrIndex,
  concrete_heads: List(PHead),
) -> List(PHead) {
  case concrete_heads {
    [HAny, ..] -> []
    [HCtr(name), ..] -> {
      let env = get_env(s)
      let ret_ty = case list.key_find(s.ctrs, name) {
        Ok(d) -> eval(s.ffi, env, d.ret_ty)
        _ -> VErr
      }
      let span = Span("", 1, 1, 1, 1)
      let ret_tag = case ret_ty {
        VCtr(tag, _) -> tag
        _ -> ""
      }
      list.key_find(index, ret_tag)
      |> result.unwrap([])
      |> list.filter_map(fn(entry) {
        let #(tag, ctr) = entry
        case unify(s, eval(s.ffi, env, ctr.ret_ty), ret_ty, span, span) {
          Ok(_) -> Ok(HCtr(tag))
          _ -> Error(Nil)
        }
      })
      |> list.filter(fn(h) { !list.contains(concrete_heads, h) })
    }
    [HRcd(_), ..] -> []
    _ -> [HAny]
  }
}

/// Check if a pattern vector is useful (not redundant) against a matrix.
///
/// Returns a list of witnesses—patterns that the vector covers but the
/// matrix doesn't. If empty, the pattern is redundant.
///
/// Algorithm:
/// - If matrix is empty, the vector is a witness (useful)
/// - If vector is empty but matrix isn't, no witnesses (redundant)
/// - Otherwise, split on the first pattern:
///   - If wildcard: check missing constructors and concrete heads
///   - If concrete: specialize matrix and recurse
pub fn useful(
  s: State,
  index: CtrIndex,
  matrix: PMatrix,
  vector: List(Pattern),
) -> List(List(Pattern)) {
  case matrix, vector {
    // If the matrix is empty, the entire vector is a valid witness
    [], _ -> [vector]
    // If we run out of columns to check, there are no witnesses (redundant)
    _, [] -> []
    _, [p, ..ps] -> {
      let #(head, hargs) = deconstruct(p)
      case head {
        HAny -> {
          let concrete_heads = get_concrete_heads(matrix)
          let missing_heads = get_missing_heads(s, index, concrete_heads)
          let missing_witnesses =
            list.flat_map(missing_heads, fn(missing) {
              let rest_witnesses = useful(s, index, default_matrix(matrix), ps)
              list.map(rest_witnesses, fn(rest) {
                let wildcards = list.repeat(PAny, head_arity(missing))
                [reconstruct(missing, wildcards), ..rest]
              })
            })
          let concrete_witnesses =
            list.flat_map(concrete_heads, fn(h) {
              let a = head_arity(h)
              let expanded_rest = list.append(list.repeat(PAny, a), ps)
              let sub_witnesses =
                useful(s, index, specialize(matrix, h), expanded_rest)
              list.map(sub_witnesses, fn(witness_row) {
                let #(args, rest) = list.split(witness_row, a)
                [reconstruct(h, args), ..rest]
              })
            })
          list.append(missing_witnesses, concrete_witnesses)
        }
        _ -> {
          // Head is concrete, specialize the matrix for it.
          let expanded_rest = list.append(hargs, ps)
          let witnesses =
            useful(s, index, specialize(matrix, head), expanded_rest)
          list.map(witnesses, fn(witness_row) {
            let a = head_arity(head)
            let #(args, rest) = list.split(witness_row, a)
            [reconstruct(head, args), ..rest]
          })
        }
      }
    }
  }
}

/// Check a list of match cases for exhaustiveness.
///
/// This is called during type checking of match expressions to verify that
/// all possible patterns are covered and no cases are redundant.
///
/// Returns a list of errors:
/// - MatchRedundantCase: A case that's already covered by previous cases
/// - MatchMissingCase: A pattern that isn't covered by any case
///
/// The algorithm builds a matrix incrementally, checking each new case
/// against what's already covered (Maranget's algorithm).
///
/// This function is pure and returns a list of errors - the caller is
/// responsible for adding them to the state via `with_err`.
pub fn check_exhaustiveness(
  s: State,
  cases: List(Case),
  span: Span,
) -> List(Error) {
  let env = get_env(s)
  // Build an index of constructors by their return type tag
  let index =
    list.fold(s.ctrs, [], fn(index, entry) {
      let #(tag, ctr) = entry
      let ret_tag = case eval(s.ffi, env, ctr.ret_ty) {
        VCtr(ret_tag, _) -> ret_tag
        _ -> ""
      }
      let existing = list.key_find(index, ret_tag) |> result.unwrap([])
      list.key_set(index, ret_tag, [#(tag, ctr), ..existing])
    })
  // Check each case for redundancy
  let #(matrix, redundant) =
    list.fold(cases, #([], []), fn(acc, c) {
      let #(matrix, diagnostics) = acc
      case useful(s, index, matrix, [c.pattern]) {
        [] -> #(matrix, [MatchRedundantCase(c.span), ..diagnostics])
        _ -> #([[c.pattern], ..matrix], diagnostics)
      }
    })
  // Check for missing cases
  let missing =
    useful(s, index, list.reverse(matrix), [PAny])
    |> list.map(fn(witness_row) {
      let witness = list.first(witness_row) |> result.unwrap(PAny)
      MatchMissingCase(span, witness)
    })
  list.append(redundant, missing)
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

// -- Error handling helpers --

/// Create an error result for infer when type checking fails.
///
/// Returns VErr for both value and type, allowing checking to continue.
fn infer_error(s: State, err: Error) -> #(Value, Type, State) {
  #(VErr, VErr, with_err(s, err))
}

/// Get a binding from the context by De Bruijn index.
///
/// The context stores (name, (value, type)) tuples, but we only need
/// the (value, type) pair for type checking.
fn ctx_get(ctx: Context, index: Int) -> Option(#(Value, Type)) {
  case list_get(ctx, index) {
    Some(#(_, pair)) -> Some(pair)
    None -> None
  }
}

/// Get element at index i from a list (0-based).
///
/// Returns None if the index is out of bounds.
/// This is used for De Bruijn index lookup in environments.
pub fn list_get(xs: List(a), i: Int) -> Option(a) {
  case xs {
    [] -> None
    [x, ..] if i == 0 -> Some(x)
    [_, ..xs] -> list_get(xs, i - 1)
  }
}

/// Generate a list of integers from start to stop (exclusive).
pub fn range(start: Int, stop: Int, step: Int) -> List(Int) {
  case start < stop {
    True -> [start, ..range(start + step, stop, step)]
    False -> []
  }
}

/// Format a span and message for error reporting.
pub fn show_msg(s: Span, msg: String) -> String {
  show_span(s) <> " " <> msg
}

/// Format a span as a string for error reporting.
pub fn show_span(s: Span) -> String {
  "["
  <> s.file
  <> ":"
  <> int.to_string(s.start_line)
  <> ":"
  <> int.to_string(s.start_col)
  <> "]"
}

/// Extract the runtime environment from the typing context.
///
/// The context stores (value, type) pairs, but for evaluation we only
/// need the values. This extracts just the values in order.
fn get_env(s: State) -> Env {
  list.map(s.ctx, fn(kv) { kv.1.0 })
}

/// Create a fresh variable for type checking.
///
/// Returns a neutral term at the current level and increments the counter.
/// Used when checking lambdas and Pi types to represent bound variables.
fn new_var(s: State) -> #(Value, State) {
  let var = VNeut(HVar(s.var), [])
  #(var, State(..s, var: s.var + 1))
}

/// Define a variable in the typing context.
///
/// Creates a fresh variable and adds it to the context with the given
/// name and type. Empty names are replaced with a generated name.
fn def_var(s: State, name: String, ty: Type) -> #(Value, State) {
  let name = case name {
    "" -> "$" <> int.to_string(s.var)
    _ -> name
  }
  let #(var, s) = new_var(s)
  #(var, State(..s, ctx: [#(name, #(var, ty)), ..s.ctx]))
}

/// Create a fresh hole (metavariable) for type checking.
///
/// Returns a neutral hole term and increments the hole counter.
/// Used when the type is unknown and should be inferred later.
fn new_hole(s: State) -> #(Value, State) {
  let hole = VNeut(HHole(s.hole), [])
  #(hole, State(..s, hole: s.hole + 1))
}
