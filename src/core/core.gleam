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
  /// Universe type at level k. See docs/core.md for details.
  Typ(universe: Int, span: Span)

  /// Literal value (42, 3.14, "hello"). Note: true/false are constructors.
  Lit(value: Literal, span: Span)

  /// Literal type (I32, F64, etc.)
  LitT(typ: LiteralType, span: Span)

  /// Bound variable (De Bruijn index). Index = distance to binder.
  Var(index: Int, span: Span)

  /// Metavariable (hole) to be solved during type checking.
  Hole(id: Int, span: Span)

  /// Error placeholder - used when parsing fails, allows error recovery
  Err(message: String, span: Span)

  /// Record with named fields.
  Rcd(fields: List(#(String, Term)), span: Span)

  /// Constructor application: #Some(42), #True(Unit), #Cons(1, Nil)
  /// Nullary constructors use Unit as argument: #True(Unit)
  Ctr(tag: String, arg: Term, span: Span)

  /// Unit value - used for nullary constructors and void
  Unit(span: Span)

  /// Field projection (record.field).
  Dot(arg: Term, field: String, span: Span)

  /// Type annotation (term : type).
  Ann(term: Term, typ: Term, span: Span)

  /// Lambda abstraction (λx. body) with optional implicit type params.
  /// implicit: list of type parameter names (e.g., ["a", "b"] for <a, b>)
  /// param: #(name, type_annotation) for the single explicit parameter
  Lam(implicit: List(String), param: #(String, Term), body: Term, span: Span)

  /// Dependent function type with implicit type params
  /// implicit: list of type parameter names (e.g., ["T", "U"] for <T, U>)
  /// name: value parameter name
  /// in: domain type
  /// out: codomain type (can mention name)
  Pi(
    implicit: List(String),
    name: String,
    in_term: Term,
    out_term: Term,
    span: Span,
  )

  /// Function application (f x) with optional implicit type args.
  /// implicit: list of type arguments (e.g., [I32, F32] for <I32, F32>)
  /// arg: single explicit argument
  App(fun: Term, implicit: List(Term), arg: Term, span: Span)

  /// Pattern matching with dependent return type.
  Match(arg: Term, motive: Term, cases: List(Case), span: Span)

  /// Built-in function call (FFI).
  Call(name: String, args: List(Term), span: Span)

  /// Compile-time evaluation block.
  Comptime(term: Term, span: Span)

  /// Fixpoint operator for recursion (fix f -> body).
  Fix(name: String, body: Term, span: Span)
}

/// Get the span from a Term.
pub fn get_span(term: Term) -> Span {
  case term {
    Typ(_, span) -> span
    Lit(_, span) -> span
    LitT(_, span) -> span
    Var(_, span) -> span
    Hole(_, span) -> span
    Err(_, span) -> span
    Rcd(_, span) -> span
    Ctr(_, _, span) -> span
    Unit(span) -> span
    Dot(_, _, span) -> span
    Ann(_, _, span) -> span
    Lam(_, _, _, span) -> span
    Pi(_, _, _, _, span) -> span
    App(_, _, _, span) -> span
    Match(_, _, _, span) -> span
    Call(_, _, span) -> span
    Comptime(_, span) -> span
    Fix(_, _, span) -> span
  }
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
  /// Closure: lambda with captured environment and implicit type params
  VLam(implicit: List(String), name: String, env: Env, body: Term)
  /// Dependent function type with implicit type params and evaluated domain
  VPi(
    implicit: List(String),
    name: String,
    env: Env,
    in_val: Value,
    out_term: Term,
  )
  /// Record type with named fields
  VRecord(fields: List(#(String, Value)))
  /// Built-in function call deferred to runtime
  /// Created when FFI not found during eval, or when args are not concrete
  VCall(name: String, args: List(Value))
  /// Fixpoint value for recursion (self-referential closure)
  VFix(name: String, env: Env, body: Term)
  /// Constructor value (algebraic data)
  VCtrValue(CtrValue)
  /// Unit value
  VUnit
  /// Error value for error recovery (continues checking after errors)
  VErr
}

/// Constructor value (runtime representation of algebraic data)
pub type CtrValue {
  /// Constructor with argument: #Some(value)
  VCtr(tag: String, arg: Value)
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
  /// Constructor pattern with arg: #Some(n), #True(Unit)
  PCtr(tag: String, arg: Pattern)
  /// Unit pattern - matches Unit value
  PUnit
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
  /// Step limit exceeded - computation was terminated to prevent infinite loop
  HStepLimit
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

// ============================================================================
// PRELUDE CONSTRUCTORS
// ============================================================================
// These constructors are automatically available in all programs.
// They define the standard library prelude types: Bool, Option, Result, Ordering.
//
// Note: Core language requires all constructors to have an argument.
// Nullary constructors use Typ(0) as a dummy unit argument.
//
// Type representation:
// - Typ(0) = Type(0) - the universe of small types
// - Typ(1) = Type(1) - the universe of large types (contains Type(0))
// - Type constructors like Option have type: Type(0) -> Type(0), represented as Typ(1)
// - Constructors return applications: Option(a) = App(Option, a)

const no_span = Span("", 0, 0, 0, 0)

/// Create initial state with default configuration and empty constructor environment.
/// Constructor definitions are populated from Tao type definitions during desugaring.
/// The core language itself has no hardcoded types - all types come from source code.
pub const initial_state = State(
  hole: 0,
  var: 0,
  ctrs: [],
  // Empty - populated from Tao type definitions
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
  #("negate", Builtin(negate_impl, [])),
]

// ============================================================================
// BUILTIN IMPLEMENTATIONS
// ============================================================================
// All builtin implementations return Option(Value):
// - Some(result) when arguments are concrete and computation succeeds
// - None when arguments are not concrete (deferred to runtime)

// ============================================================================
// Helper functions for builtin implementations

/// Generic binary operation helper for all numeric types.
fn binop_all(
  args: List(Value),
  i32_op: fn(Int, Int) -> Int,
  i64_op: fn(Int, Int) -> Int,
  u32_op: fn(Int, Int) -> Int,
  u64_op: fn(Int, Int) -> Int,
  f32_op: fn(Float, Float) -> Float,
  f64_op: fn(Float, Float) -> Float,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(i32_op(a, b))))
    [VLit(I64(a)), VLit(I64(b))] -> Some(VLit(I64(i64_op(a, b))))
    [VLit(U32(a)), VLit(U32(b))] -> Some(VLit(U32(u32_op(a, b))))
    [VLit(U64(a)), VLit(U64(b))] -> Some(VLit(U64(u64_op(a, b))))
    [VLit(F32(a)), VLit(F32(b))] -> Some(VLit(F32(f32_op(a, b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(f64_op(a, b))))
    _ -> None
  }
}

/// Binary operation helper for integer types only (I32, I64, U32, U64).
fn binop_int(
  args: List(Value),
  i32_op: fn(Int, Int) -> Int,
  i64_op: fn(Int, Int) -> Int,
  u32_op: fn(Int, Int) -> Int,
  u64_op: fn(Int, Int) -> Int,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(i32_op(a, b))))
    [VLit(I64(a)), VLit(I64(b))] -> Some(VLit(I64(i64_op(a, b))))
    [VLit(U32(a)), VLit(U32(b))] -> Some(VLit(U32(u32_op(a, b))))
    [VLit(U64(a)), VLit(U64(b))] -> Some(VLit(U64(u64_op(a, b))))
    _ -> None
  }
}

/// Binary operation helper for I32 and F64 only (legacy helper).
fn binop_i32_f64(
  args: List(Value),
  i32_op: fn(Int, Int) -> Int,
  f64_op: fn(Float, Float) -> Float,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(i32_op(a, b))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(F64(f64_op(a, b))))
    _ -> None
  }
}

/// Generic comparison helper for all numeric types.
fn cmp_all(
  args: List(Value),
  i32_cmp: fn(Int, Int) -> Bool,
  i64_cmp: fn(Int, Int) -> Bool,
  u32_cmp: fn(Int, Int) -> Bool,
  u64_cmp: fn(Int, Int) -> Bool,
  f32_cmp: fn(Float, Float) -> Bool,
  f64_cmp: fn(Float, Float) -> Bool,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(i32_cmp(a, b)))))
    [VLit(I64(a)), VLit(I64(b))] -> Some(VLit(I32(bool_to_int(i64_cmp(a, b)))))
    [VLit(U32(a)), VLit(U32(b))] -> Some(VLit(I32(bool_to_int(u32_cmp(a, b)))))
    [VLit(U64(a)), VLit(U64(b))] -> Some(VLit(I32(bool_to_int(u64_cmp(a, b)))))
    [VLit(F32(a)), VLit(F32(b))] -> Some(VLit(I32(bool_to_int(f32_cmp(a, b)))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(f64_cmp(a, b)))))
    _ -> None
  }
}

/// Comparison helper for I32 and F64 only (legacy helper).
fn cmp_i32_f64(
  args: List(Value),
  i32_cmp: fn(Int, Int) -> Bool,
  f64_cmp: fn(Float, Float) -> Bool,
) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] -> Some(VLit(I32(bool_to_int(i32_cmp(a, b)))))
    [VLit(F64(a)), VLit(F64(b))] -> Some(VLit(I32(bool_to_int(f64_cmp(a, b)))))
    _ -> None
  }
}

// ============================================================================
// Arithmetic operations

pub fn add_impl(args: List(Value)) -> Option(Value) {
  binop_all(
    args,
    fn(a, b) { a + b },
    fn(a, b) { a + b },
    fn(a, b) { a + b },
    fn(a, b) { a + b },
    fn(a, b) { a +. b },
    fn(a, b) { a +. b },
  )
}

pub fn sub_impl(args: List(Value)) -> Option(Value) {
  binop_all(
    args,
    fn(a, b) { a - b },
    fn(a, b) { a - b },
    fn(a, b) { a - b },
    fn(a, b) { a - b },
    fn(a, b) { a -. b },
    fn(a, b) { a -. b },
  )
}

pub fn mul_impl(args: List(Value)) -> Option(Value) {
  binop_all(
    args,
    fn(a, b) { a * b },
    fn(a, b) { a * b },
    fn(a, b) { a * b },
    fn(a, b) { a * b },
    fn(a, b) { a *. b },
    fn(a, b) { a *. b },
  )
}

pub fn div_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a)), VLit(I32(b))] if b != 0 -> Some(VLit(I32(a / b)))
    [VLit(I64(a)), VLit(I64(b))] if b != 0 -> Some(VLit(I64(a / b)))
    [VLit(U32(a)), VLit(U32(b))] if b != 0 -> Some(VLit(U32(a / b)))
    [VLit(U64(a)), VLit(U64(b))] if b != 0 -> Some(VLit(U64(a / b)))
    [VLit(F32(a)), VLit(F32(b))] if b != 0.0 -> Some(VLit(F32(a /. b)))
    [VLit(F64(a)), VLit(F64(b))] if b != 0.0 -> Some(VLit(F64(a /. b)))
    _ -> None
  }
}

pub fn mod_impl(args: List(Value)) -> Option(Value) {
  binop_int(
    args,
    fn(a, b) { a % b },
    fn(a, b) { a % b },
    fn(a, b) { a % b },
    fn(a, b) { a % b },
  )
}

// ============================================================================
// Comparison operations

pub fn eq_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a == b },
    fn(a, b) { a == b },
    fn(a, b) { a == b },
    fn(a, b) { a == b },
    fn(a, b) { a == b },
    fn(a, b) { a == b },
  )
}

pub fn neq_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a != b },
    fn(a, b) { a != b },
    fn(a, b) { a != b },
    fn(a, b) { a != b },
    fn(a, b) { a != b },
    fn(a, b) { a != b },
  )
}

pub fn lt_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a < b },
    fn(a, b) { a < b },
    fn(a, b) { a < b },
    fn(a, b) { a < b },
    fn(a, b) { a <. b },
    fn(a, b) { a <. b },
  )
}

pub fn lte_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a <= b },
    fn(a, b) { a <= b },
    fn(a, b) { a <= b },
    fn(a, b) { a <= b },
    fn(a, b) { a <=. b },
    fn(a, b) { a <=. b },
  )
}

pub fn gt_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a > b },
    fn(a, b) { a > b },
    fn(a, b) { a > b },
    fn(a, b) { a > b },
    fn(a, b) { a >. b },
    fn(a, b) { a >. b },
  )
}

pub fn gte_impl(args: List(Value)) -> Option(Value) {
  cmp_all(
    args,
    fn(a, b) { a >= b },
    fn(a, b) { a >= b },
    fn(a, b) { a >= b },
    fn(a, b) { a >= b },
    fn(a, b) { a >=. b },
    fn(a, b) { a >=. b },
  )
}

// ============================================================================
// Logical operations

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

pub fn negate_impl(args: List(Value)) -> Option(Value) {
  case args {
    [VLit(I32(a))] -> Some(VLit(I32(-a)))
    [VLit(I64(a))] -> Some(VLit(I64(-a)))
    [VLit(F32(a))] -> Some(VLit(F32(0.0 -. a)))
    [VLit(F64(a))] -> Some(VLit(F64(0.0 -. a)))
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
  case term {
    Call(name, args, _) -> {
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
                ComptimePermissionDenied(name, get_span(term), required_perms)
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

  // Type errors - consistent naming: Problem + Context
  TypeMismatch(expected: Type, got: Type, expected_span: Span, got_span: Span)
  PatternMismatch(
    pattern: Pattern,
    expected_type: Type,
    pattern_span: Span,
    value_span: Span,
  )
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

  // Exhaustiveness checks - consistent naming: Match + Issue
  MatchMissingCase(span: Span, pattern: Pattern)
  MatchRedundantCase(span: Span)

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

/// Shift all free variable indices in a term by a given amount.
/// This is used when adding a new binder to the environment.
fn shift_term(term: Term, shift: Int) -> Term {
  case term {
    Var(i, span) -> Var(i + shift, span)
    Lam(implicit, param, body, span) -> {
      Lam(implicit, param, shift_term(body, shift), span)
    }
    Pi(implicit, name, in_term, out_term, span) -> {
      Pi(
        implicit,
        name,
        shift_term(in_term, shift),
        shift_term(out_term, shift),
        span,
      )
    }
    App(fun, implicit, arg, span) -> {
      App(shift_term(fun, shift), implicit, shift_term(arg, shift), span)
    }
    Match(arg, motive, cases, span) -> {
      Match(
        shift_term(arg, shift),
        shift_term(motive, shift),
        list.map(cases, fn(c) { shift_case(c, shift) }),
        span,
      )
    }
    Hole(id, span) -> Hole(id, span)
    Typ(k, span) -> Typ(k, span)
    Lit(k, span) -> Lit(k, span)
    LitT(k, span) -> LitT(k, span)
    Rcd(fields, span) ->
      Rcd(list.map(fields, fn(kv) { #(kv.0, shift_term(kv.1, shift)) }), span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_term(arg, shift), span)
    Unit(span) -> Unit(span)
    Dot(arg, name, span) -> Dot(shift_term(arg, shift), name, span)
    Ann(term, type_ann, span) ->
      Ann(shift_term(term, shift), shift_term(type_ann, shift), span)
    Call(name, args, span) ->
      Call(name, list.map(args, fn(a) { shift_term(a, shift) }), span)
    Comptime(term, span) -> Comptime(shift_term(term, shift), span)
    Fix(name, body, span) -> Fix(name, shift_term(body, shift), span)
    Err(msg, span) -> Err(msg, span)
  }
}

fn shift_case(case_val: Case, shift: Int) -> Case {
  case case_val {
    Case(pattern, body, guard, span) ->
      Case(
        pattern,
        shift_term(body, shift),
        option.map(guard, fn(g) { shift_term(g, shift) }),
        span,
      )
  }
}

/// Evaluate a term to its normal form in the given environment.
///
/// The environment maps De Bruijn indices to values. When evaluating:
/// - Variables look up their index in the environment
/// - Lambdas become closures (capturing the current environment)
/// - Applications evaluate the function and argument, then apply
/// - Neutral terms are created when computation is stuck on unknowns
pub fn eval(ffi: FFI, env: Env, term: Term) -> Value {
  eval_with_steps(ffi, env, term, 1_000_000)
  // Increased step limit for deep recursion
}

/// Evaluate a term to a value with a step limit to prevent infinite loops.
/// When the step limit is exceeded, returns a neutral term.
fn eval_with_steps(ffi: FFI, env: Env, term: Term, max_steps: Int) -> Value {
  eval_loop(ffi, env, term, 0, max_steps)
}

fn eval_loop(
  ffi: FFI,
  env: Env,
  term: Term,
  steps: Int,
  max_steps: Int,
) -> Value {
  // Check step limit
  case steps >= max_steps {
    True -> VNeut(HStepLimit, [])
    // Return neutral term when limit exceeded
    False -> eval_step(ffi, env, term, steps, max_steps)
  }
}

fn eval_step(
  ffi: FFI,
  env: Env,
  term: Term,
  steps: Int,
  max_steps: Int,
) -> Value {
  case term {
    Typ(k, _) -> VTyp(k)
    Lit(k, _) -> VLit(k)
    LitT(k, _) -> VLitT(k)
    Var(i, _) ->
      case list_get(env, i) {
        Some(value) -> value
        None -> VErr
      }
    Hole(id, _) -> VNeut(HHole(id), [])
    Rcd(fields, _) ->
      VRcd(
        list.map(fields, fn(kv) {
          #(kv.0, eval_loop(ffi, env, kv.1, steps + 1, max_steps))
        }),
      )
    Ctr(tag, arg, _) ->
      VCtrValue(VCtr(tag, eval_loop(ffi, env, arg, steps + 1, max_steps)))
    Unit(_) -> VUnit
    Dot(arg, name, _) ->
      do_dot(
        ffi,
        eval_loop(ffi, env, arg, steps + 1, max_steps),
        name,
        steps + 1,
        max_steps,
      )
    Ann(term, _, _) -> eval_loop(ffi, env, term, steps + 1, max_steps)
    Lam(implicit, param, body, _) -> {
      let #(name, _) = param
      VLam(implicit, name, env, body)
    }
    Pi(implicit, name, in_term, out_term, _) ->
      VPi(
        implicit,
        name,
        env,
        eval_loop(ffi, env, in_term, steps + 1, max_steps),
        out_term,
      )
    App(fun, implicit, arg, _) -> {
      // Evaluate function and argument
      let fun_val = eval_loop(ffi, env, fun, steps + 1, max_steps)
      let arg_val = eval_loop(ffi, env, arg, steps + 1, max_steps)

      // Handle implicit arguments recursively
      case implicit {
        [] -> {
          // Base case: no implicit args, apply normally
          do_app(ffi, fun_val, arg_val, steps + 1, max_steps)
        }
        [implicit_arg, ..rest] -> {
          // Recursive case: peel off one implicit arg
          let implicit_val =
            eval_loop(ffi, env, implicit_arg, steps + 1, max_steps)
          // Instantiate function with implicit and recurse
          let instantiated = do_app_implicit(fun_val, implicit_val)
          do_app_with_implicit(
            ffi,
            instantiated,
            rest,
            arg_val,
            steps + 1,
            max_steps,
          )
        }
      }
    }
    Match(arg, motive, cases, _) -> {
      let arg_val = eval_loop(ffi, env, arg, steps + 1, max_steps)
      let motive_val = eval_loop(ffi, env, motive, steps + 1, max_steps)
      do_match(ffi, env, arg_val, motive_val, cases, steps + 1, max_steps)
    }
    Call(name, args, _) -> {
      // Evaluate all arguments first
      let arg_vals =
        list.map(args, eval_loop(ffi, env, _, steps + 1, max_steps))
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
    Comptime(term, _) -> eval_loop(ffi, env, term, steps + 1, max_steps)
    Fix(name, body, _) -> VFix(name, env, body)
    Err(_, _) -> VErr
    // Error terms evaluate to VErr
  }
}

/// Evaluate a field projection.
///
/// If the value is neutral (unknown), the projection is added to the spine.
/// If the value is a record, the field is looked up immediately.
fn do_dot(
  ffi: FFI,
  value: Value,
  name: String,
  steps: Int,
  max_steps: Int,
) -> Value {
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
pub fn do_app(
  ffi: FFI,
  fun: Value,
  arg: Value,
  steps: Int,
  max_steps: Int,
) -> Value {
  case fun {
    VNeut(head, spine) -> VNeut(head, [EApp(arg), ..spine])
    VLam(_, _, env, body) ->
      eval_loop(ffi, [arg, ..env], body, steps + 1, max_steps)
    VFix(name, env, body) -> {
      // Unfold fixpoint: evaluate the body with the fixpoint in the environment.
      // For recursive functions, the body is a lambda, so this creates a closure.
      // For self-referential fixpoints like (fix f -> f), we detect the loop and
      // return a neutral term to avoid infinite recursion.
      let fix_val = VFix(name, env, body)
      let body_val =
        eval_loop(ffi, [fix_val, ..env], body, steps + 1, max_steps)
      // Check if body evaluated to the same fixpoint (self-reference)
      case body_val {
        VFix(n2, _, _) if n2 == name -> {
          // Self-referential fixpoint - return neutral term to avoid infinite loop
          VNeut(HVar(0), [EApp(arg)])
        }
        _ -> do_app(ffi, body_val, arg, steps + 1, max_steps)
      }
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
fn do_app_with_implicit(
  ffi: FFI,
  fun: Value,
  implicit: List(Term),
  arg: Value,
  steps: Int,
  max_steps: Int,
) -> Value {
  case implicit {
    [] -> do_app(ffi, fun, arg, steps, max_steps)
    [implicit_arg, ..rest] -> {
      // This shouldn't happen in normal evaluation - implicit args should be
      // handled during the initial App evaluation
      // But handle it recursively just in case
      let implicit_val = eval_loop(ffi, [], implicit_arg, steps + 1, max_steps)
      let instantiated = do_app_implicit(fun, implicit_val)
      do_app_with_implicit(ffi, instantiated, rest, arg, steps + 1, max_steps)
    }
  }
}

/// Evaluate a pattern match.
///
/// If the argument is neutral (unknown), the match is delayed by adding it to
/// the spine. Otherwise, we try to match the argument against each case.
///
/// The motive is the return type of the match (for dependent pattern matching).
pub fn do_match(
  ffi: FFI,
  env: Env,
  arg: Value,
  motive: Value,
  cases: List(Case),
  steps: Int,
  max_steps: Int,
) -> Value {
  case arg {
    VNeut(head, spine) -> VNeut(head, [EMatch(env, motive, cases), ..spine])
    _ ->
      case do_match_cases(arg, cases, steps + 1, max_steps) {
        Some(#(bindings, body)) ->
          eval_loop(ffi, list.append(bindings, env), body, steps + 1, max_steps)
        None -> VErr
      }
  }
}

/// Try to match a value against a list of cases, returning the first match.
///
/// Returns the bindings (environment) and body of the matching case.
pub fn do_match_cases(
  arg: Value,
  cases: List(Case),
  steps: Int,
  max_steps: Int,
) -> Option(#(Env, Term)) {
  case cases {
    [] -> None
    [c, ..cases] ->
      case do_match_pattern(c.pattern, arg) {
        Ok(env) -> {
          // Check guard if present
          case c.guard {
            Some(guard_term) -> {
              // Evaluate guard in the extended environment
              let guard_val =
                eval_loop([], env, guard_term, steps + 1, max_steps)
              // For now, treat any non-error guard value as true
              // (proper boolean checking would be better)
              case guard_val {
                VErr -> do_match_cases(arg, cases, steps + 1, max_steps)
                _ -> Some(#(env, c.body))
              }
            }
            None -> Some(#(env, c.body))
          }
        }
        Error(Nil) -> do_match_cases(arg, cases, steps + 1, max_steps)
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
    PCtr(ptag, parg), VCtrValue(VCtr(vtag, varg)) if ptag == vtag ->
      do_match_pattern(parg, varg)
    PCtr("True", PUnit), VCtrValue(VCtr("True", VUnit)) -> Ok([])
    PCtr("False", PUnit), VCtrValue(VCtr("False", VUnit)) -> Ok([])
    PCtr("None", PUnit), VCtrValue(VCtr("None", VUnit)) -> Ok([])
    PCtr("LT", PUnit), VCtrValue(VCtr("LT", VUnit)) -> Ok([])
    PCtr("EQ", PUnit), VCtrValue(VCtr("EQ", VUnit)) -> Ok([])
    PCtr("GT", PUnit), VCtrValue(VCtr("GT", VUnit)) -> Ok([])
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

/// Quote a value back to syntax (reification) with default step limit.
///
/// The level parameter tracks the current De Bruijn level. When quoting a
/// lambda, we create a fresh neutral variable at the current level, apply it
/// to the body, and quote the result. This converts De Bruijn levels back to
/// indices using the formula: index = lvl - level - 1.
pub fn quote(ffi: FFI, lvl: Int, value: Value, s: Span) -> Term {
  quote_with_steps(ffi, lvl, value, s, 1_000_000)
  // High step limit for deep trees
}

/// Quote a value back to syntax with a step counter to prevent infinite loops.
///
/// When the step limit is exceeded, returns a neutral term with HStepLimit head.
fn quote_with_steps(
  ffi: FFI,
  lvl: Int,
  value: Value,
  s: Span,
  steps: Int,
) -> Term {
  case steps {
    0 -> VNeut(HStepLimit, []) |> quote(ffi, lvl, _, s)
    // Return stuck term
    _ -> quote_loop(ffi, lvl, value, s, steps)
  }
}

fn quote_loop(ffi: FFI, lvl: Int, value: Value, s: Span, steps: Int) -> Term {
  case value {
    VTyp(k) -> Typ(k, s)
    VLit(k) -> Lit(k, s)
    VLitT(k) -> LitT(k, s)
    VNeut(head, spine) -> {
      let head_term = quote_head(lvl, head, s)
      quote_neut_with_steps(ffi, lvl, head_term, spine, s, steps)
    }
    VRcd(fields) ->
      Rcd(
        list.map(fields, fn(kv) {
          #(kv.0, quote_with_steps(ffi, lvl, kv.1, s, steps - 1))
        }),
        s,
      )
    VCtrValue(VCtr(tag, arg)) ->
      Ctr(tag, quote_with_steps(ffi, lvl, arg, s, steps - 1), s)
    VUnit -> Unit(s)
    VLam(implicit, name, env, body) -> {
      // Quote the body term directly without re-evaluation.
      // Re-evaluation causes exponential blowup for recursive functions.
      // Extend env with a fresh neutral for the parameter (Var(0) in the body).
      let fresh = VNeut(HVar(lvl), [])
      let body_quote =
        quote_term_in_env(
          ffi,
          lvl + 1,
          body,
          [fresh, ..env],
          get_span(body),
          steps - 1,
        )
      // Quote the parameter type from the fresh variable to preserve hole info
      let param_ty_quote = quote_with_steps(ffi, lvl, fresh, s, steps - 1)
      Lam(implicit, #(name, param_ty_quote), body_quote, s)
    }
    VPi(implicit, name, env, in_val, out_term) -> {
      // Quote the domain (already evaluated)
      let in_quote = quote_with_steps(ffi, lvl, in_val, s, steps - 1)
      // Quote the codomain term directly without re-evaluation
      // Extend env with a fresh neutral for the domain variable (Var(0) in out_term).
      let fresh = VNeut(HVar(lvl), [])
      let out_quote =
        quote_term_in_env(
          ffi,
          lvl + 1,
          out_term,
          [fresh, ..env],
          get_span(out_term),
          steps - 1,
        )
      Pi(implicit, name, in_quote, out_quote, s)
    }
    VRecord(fields) -> {
      // Record type - quote each field type
      Rcd(
        list.map(fields, fn(kv) {
          #(kv.0, quote_with_steps(ffi, lvl, kv.1, s, steps - 1))
        }),
        s,
      )
    }
    VCall(name, args) -> {
      // Quote stuck built-in with collected args
      Call(
        name,
        list.map(args, fn(a) { quote_with_steps(ffi, lvl, a, s, steps - 1) }),
        s,
      )
    }
    VFix(name, env, body) -> {
      // Quote the body term directly without re-evaluation.
      // Re-evaluation causes exponential blowup for recursive functions.
      let fix_val = VFix(name, env, body)
      let body_quote =
        quote_term_in_env(
          ffi,
          lvl + 1,
          body,
          [fix_val, ..env],
          get_span(body),
          steps - 1,
        )
      Fix(name, body_quote, s)
    }
    VErr -> Hole(-1, s)
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

/// Quote a neutral term with step counter.
fn quote_neut_with_steps(
  ffi: FFI,
  lvl: Int,
  head: Term,
  spine: List(Elim),
  s: Span,
  steps: Int,
) -> Term {
  list.fold_right(spine, head, fn(head, elim) {
    quote_elim_with_steps(ffi, lvl, head, elim, s, steps)
  })
}

/// Quote a single elimination (spine element).
fn quote_elim(ffi: FFI, lvl: Int, head: Term, elim: Elim, s: Span) -> Term {
  case elim {
    EDot(name) -> Dot(head, name, s)
    EApp(arg) -> App(head, [], quote(ffi, lvl, arg, s), s)
    EAppImplicit(implicit_val) -> {
      // Implicit application - add to implicit list
      // For now, just quote the implicit value
      // This creates a term like: head<implicit_val>()
      // We need to handle this specially
      App(head, [quote(ffi, lvl, implicit_val, s)], Hole(-1, s), s)
    }
    // The env is discarded because we're reconstructing syntax, not evaluating.
    // The cases bodies are already Terms (syntax), not Values, so they don't
    // need quoting. The env was only needed during evaluation to capture the
    // closure environment for delayed matching on neutral terms.
    EMatch(_, motive, cases) ->
      Match(head, quote(ffi, lvl, motive, s), cases, s)
  }
}

/// Quote a single elimination (spine element) with step counter.
fn quote_elim_with_steps(
  ffi: FFI,
  lvl: Int,
  head: Term,
  elim: Elim,
  s: Span,
  steps: Int,
) -> Term {
  case elim {
    EDot(name) -> Dot(head, name, s)
    EApp(arg) -> App(head, [], quote_with_steps(ffi, lvl, arg, s, steps - 1), s)
    EAppImplicit(implicit_val) -> {
      App(
        head,
        [quote_with_steps(ffi, lvl, implicit_val, s, steps - 1)],
        Hole(-1, s),
        s,
      )
    }
    EMatch(_, motive, cases) ->
      Match(head, quote_with_steps(ffi, lvl, motive, s, steps - 1), cases, s)
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
    HVar(l) -> Var(lvl - l - 1, s)
    HHole(id) -> Hole(id, s)
    HStepLimit -> Hole(-1, s)
    // Step limit exceeded - represent as hole
  }
}

/// Quote a term that represents a value in a given environment.
///
/// This is used for quoting lambda/fix bodies without re-evaluation.
/// The environment provides the values for free variables in the term.
///
/// CRITICAL: This function does NOT evaluate - it only quotes terms to syntax.
/// This prevents exponential blowup when quoting recursive functions.
fn quote_term_in_env(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case steps {
    0 -> Hole(-1, s)
    _ -> quote_term_in_env_loop(ffi, lvl, term, env, s, steps)
  }
}

fn quote_term_in_env_loop(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case term {
    Var(i, span) -> {
      // Look up in environment and quote the value
      case list_get(env, i) {
        Some(value) -> quote_with_steps(ffi, lvl, value, span, steps - 1)
        None -> Var(i, span)
      }
    }

    Lam(implicit, param, body, span) -> {
      // Extend environment with a fresh neutral for the parameter
      let fresh = VNeut(HVar(lvl), [])
      let body_quote =
        quote_term_in_env(ffi, lvl + 1, body, [fresh, ..env], span, steps - 1)
      Lam(implicit, param, body_quote, span)
    }

    Pi(implicit, name, in_term, out_term, span) -> {
      let in_quote = quote_term_in_env(ffi, lvl, in_term, env, span, steps - 1)
      let fresh = VNeut(HVar(lvl), [])
      let out_quote =
        quote_term_in_env(
          ffi,
          lvl + 1,
          out_term,
          [fresh, ..env],
          span,
          steps - 1,
        )
      Pi(implicit, name, in_quote, out_quote, span)
    }

    Fix(name, body, span) -> {
      // Fix in a term - extend env with the fix itself
      let fix_val = VFix(name, env, body)
      let body_quote =
        quote_term_in_env(ffi, lvl + 1, body, [fix_val, ..env], span, steps - 1)
      Fix(name, body_quote, span)
    }

    App(fun, implicit, arg, span) -> {
      let fun_quote = quote_term_in_env(ffi, lvl, fun, env, span, steps - 1)
      let arg_quote = quote_term_in_env(ffi, lvl, arg, env, span, steps - 1)
      let implicit_quote =
        list.map(implicit, quote_term_in_env(ffi, lvl, _, env, span, steps - 1))
      App(fun_quote, implicit_quote, arg_quote, span)
    }

    Match(arg, motive, cases, span) -> {
      let arg_quote = quote_term_in_env(ffi, lvl, arg, env, span, steps - 1)
      let motive_quote =
        quote_term_in_env(ffi, lvl, motive, env, span, steps - 1)
      let cases_quote =
        list.map(cases, fn(c) {
          Case(
            c.pattern,
            quote_term_in_env(ffi, lvl, c.body, env, c.span, steps - 1),
            c.guard,
            c.span,
          )
        })
      Match(arg_quote, motive_quote, cases_quote, span)
    }

    Call(name, args, span) -> {
      let args_quote =
        list.map(args, quote_term_in_env(ffi, lvl, _, env, span, steps - 1))
      Call(name, args_quote, span)
    }

    Rcd(fields, span) -> {
      let fields_quote =
        list.map(fields, fn(kv) {
          #(kv.0, quote_term_in_env(ffi, lvl, kv.1, env, span, steps - 1))
        })
      Rcd(fields_quote, span)
    }

    Ctr(tag, arg, span) -> {
      Ctr(tag, quote_term_in_env(ffi, lvl, arg, env, span, steps - 1), span)
    }

    Dot(arg, name, span) -> {
      Dot(quote_term_in_env(ffi, lvl, arg, env, span, steps - 1), name, span)
    }

    Ann(inner, typ, span) -> {
      Ann(quote_term_in_env(ffi, lvl, inner, env, span, steps - 1), typ, span)
    }

    Comptime(inner, span) -> {
      Comptime(quote_term_in_env(ffi, lvl, inner, env, span, steps - 1), span)
    }

    // For literal/value terms, quote directly
    Lit(k, span) -> Lit(k, span)
    Typ(k, span) -> Typ(k, span)
    LitT(k, span) -> LitT(k, span)
    Hole(id, span) -> Hole(id, span)
    Unit(span) -> Unit(span)
    Err(msg, span) -> Err(msg, span)
  }
}

// ============================================================================
// UNIFICATION
// ============================================================================
// Unification solves metavariables by comparing two values and accumulating
// solutions in the substitution. It implements higher-order unification with
// an occurs check to prevent infinite types.

/// Collect all free hole IDs in a value (after forcing the substitution).
pub fn free_holes(sub: Subst, value: Value) -> List(Int) {
  free_holes_value(sub, value)
}

/// Collect free hole IDs in a value (alias for free_holes).
pub fn free_holes_value(sub: Subst, value: Value) -> List(Int) {
  case force([], sub, value) {
    VTyp(_) | VLit(_) | VLitT(_) | VErr | VUnit -> []
    VNeut(HHole(hole_id), spine) ->
      list.append([hole_id], list.flat_map(spine, free_holes_elim(sub, _)))
    VNeut(HStepLimit, spine) -> list.flat_map(spine, free_holes_elim(sub, _))
    VNeut(_, spine) -> list.flat_map(spine, free_holes_elim(sub, _))
    VRcd(fields) ->
      list.flat_map(fields, fn(kv) { free_holes_value(sub, kv.1) })
    VCtrValue(VCtr(_, arg)) -> free_holes_value(sub, arg)
    VLam(_, _, env, body) ->
      list.append(
        list.flat_map(env, free_holes_value(sub, _)),
        free_holes_term(sub, body),
      )
    VPi(_, _, env, in_val, out_term) ->
      list.append(
        list.flat_map(env, free_holes_value(sub, _)),
        list.append(
          free_holes_value(sub, in_val),
          free_holes_term(sub, out_term),
        ),
      )
    VCall(_, args) -> list.flat_map(args, free_holes_value(sub, _))
    VFix(_, env, body) ->
      list.append(
        list.flat_map(env, free_holes_value(sub, _)),
        free_holes_term(sub, body),
      )
    VRecord(fields) ->
      list.flat_map(fields, fn(kv) { free_holes_value(sub, kv.1) })
  }
}

/// Collect free hole IDs in a term.
fn free_holes_term(sub: Subst, term: Term) -> List(Int) {
  case term {
    Typ(_, _)
    | Lit(_, _)
    | LitT(_, _)
    | Var(_, _)
    | Hole(_, _)
    | Err(_, _)
    | Unit(_) -> []
    Rcd(fields, _) ->
      list.flat_map(fields, fn(kv) { free_holes_term(sub, kv.1) })
    Ctr(_, arg, _) -> free_holes_term(sub, arg)
    Dot(arg, _, _) -> free_holes_term(sub, arg)
    Ann(term, typ, _) ->
      list.append(free_holes_term(sub, term), free_holes_term(sub, typ))
    Lam(_, _, body, _) -> free_holes_term(sub, body)
    Pi(_, _, in_term, out_term, _) ->
      list.append(free_holes_term(sub, in_term), free_holes_term(sub, out_term))
    App(fun, implicit, arg, _) ->
      list.append(
        free_holes_term(sub, fun),
        list.append(
          list.flat_map(implicit, free_holes_term(sub, _)),
          free_holes_term(sub, arg),
        ),
      )
    Match(arg, motive, cases, _) ->
      list.append(
        free_holes_term(sub, arg),
        list.append(
          free_holes_term(sub, motive),
          list.flat_map(cases, fn(c) { free_holes_term(sub, c.body) }),
        ),
      )
    Call(_, args, _) -> list.flat_map(args, free_holes_term(sub, _))
    Comptime(term, _) -> free_holes_term(sub, term)
    Fix(_, body, _) -> free_holes_term(sub, body)
  }
}

/// Collect free holes in an elimination (spine element).
fn free_holes_elim(sub: Subst, elim: Elim) -> List(Int) {
  case elim {
    EDot(_) -> []
    EApp(arg) -> free_holes(sub, arg)
    EAppImplicit(arg) -> free_holes(sub, arg)
    EMatch(env, motive, cases) ->
      list.append(
        list.flat_map(env, free_holes(sub, _)),
        free_holes(sub, motive),
      )
  }
}

/// Collect free hole IDs in a value WITHOUT forcing substitution.
/// This is used during generalization to find holes before they're solved.
fn free_holes_in_value(sub: Subst, value: Value) -> List(Int) {
  case value {
    VTyp(_) | VLit(_) | VLitT(_) | VErr | VUnit -> []
    VNeut(HHole(hole_id), spine) ->
      list.append([hole_id], list.flat_map(spine, free_holes_in_elim(sub, _)))
    VNeut(HStepLimit, spine) -> list.flat_map(spine, free_holes_in_elim(sub, _))
    VNeut(_, spine) -> list.flat_map(spine, free_holes_in_elim(sub, _))
    VRcd(fields) ->
      list.flat_map(fields, fn(kv) { free_holes_in_value(sub, kv.1) })
    VCtrValue(VCtr(_, arg)) -> free_holes_in_value(sub, arg)
    VLam(_, _, env, body) ->
      list.append(
        list.flat_map(env, free_holes_in_value(sub, _)),
        free_holes_in_term_direct(body),
      )
    VPi(_, _, env, in_val, out_term) ->
      list.append(
        list.flat_map(env, free_holes_in_value(sub, _)),
        list.append(
          free_holes_in_value(sub, in_val),
          free_holes_in_term_direct(out_term),
        ),
      )
    VCall(_, args) -> list.flat_map(args, free_holes_in_value(sub, _))
    VFix(_, env, body) ->
      list.append(
        list.flat_map(env, free_holes_in_value(sub, _)),
        free_holes_in_term_direct(body),
      )
    VRecord(fields) ->
      list.flat_map(fields, fn(kv) { free_holes_in_value(sub, kv.1) })
  }
}

/// Collect free hole IDs in a term directly (no substitution needed).
fn free_holes_in_term_direct(term: Term) -> List(Int) {
  case term {
    Typ(_, _) | Lit(_, _) | LitT(_, _) | Var(_, _) | Unit(_) -> []
    Hole(id, _) -> [id]
    Err(_, _) -> []
    Rcd(fields, _) ->
      list.flat_map(fields, fn(kv) { free_holes_in_term_direct(kv.1) })
    Ctr(_, arg, _) -> free_holes_in_term_direct(arg)
    Dot(arg, _, _) -> free_holes_in_term_direct(arg)
    Ann(term, typ, _) ->
      list.append(
        free_holes_in_term_direct(term),
        free_holes_in_term_direct(typ),
      )
    Lam(_, _, body, _) -> free_holes_in_term_direct(body)
    Pi(_, _, in_term, out_term, _) ->
      list.append(
        free_holes_in_term_direct(in_term),
        free_holes_in_term_direct(out_term),
      )
    App(fun, implicit, arg, _) ->
      list.append(
        free_holes_in_term_direct(fun),
        list.append(
          list.flat_map(implicit, free_holes_in_term_direct),
          free_holes_in_term_direct(arg),
        ),
      )
    Match(arg, motive, cases, _) ->
      list.append(
        free_holes_in_term_direct(arg),
        list.append(
          free_holes_in_term_direct(motive),
          list.flat_map(cases, fn(c) { free_holes_in_term_direct(c.body) }),
        ),
      )
    Call(_, args, _) -> list.flat_map(args, free_holes_in_term_direct)
    Comptime(term, _) -> free_holes_in_term_direct(term)
    Fix(_, body, _) -> free_holes_in_term_direct(body)
  }
}

/// Collect free holes in an elimination without forcing substitution.
fn free_holes_in_elim(sub: Subst, elim: Elim) -> List(Int) {
  case elim {
    EDot(_) -> []
    EApp(arg) -> free_holes_in_value(sub, arg)
    EAppImplicit(arg) -> free_holes_in_value(sub, arg)
    EMatch(env, motive, cases) ->
      list.append(
        list.flat_map(env, free_holes_in_value(sub, _)),
        free_holes_in_value(sub, motive),
      )
  }
}

/// Collect all existing names (implicit params and value vars) from a term and implicit list.
/// Used to generate unique names that don't shadow existing ones.
fn collect_existing_names(implicit: List(String), term: Term) -> List(String) {
  list.append(implicit, collect_names_from_term(term))
}

fn collect_names_from_term(term: Term) -> List(String) {
  collect_names_from_term_acc(term, [])
}

fn collect_names_from_term_acc(term: Term, acc: List(String)) -> List(String) {
  case term {
    Typ(_, _)
    | Lit(_, _)
    | LitT(_, _)
    | Var(_, _)
    | Hole(_, _)
    | Err(_, _)
    | Unit(_) -> acc
    Rcd(fields, _) -> collect_names_from_fields_acc(fields, acc)
    Ctr(_, arg, _) -> collect_names_from_term_acc(arg, acc)
    Dot(arg, _, _) -> collect_names_from_term_acc(arg, acc)
    Ann(term, typ, _) -> {
      let acc1 = collect_names_from_term_acc(term, acc)
      collect_names_from_term_acc(typ, acc1)
    }
    Lam(impl, #(name, _), body, _) -> {
      let acc1 = list.append(acc, impl)
      let acc2 = [name, ..acc1]
      collect_names_from_term_acc(body, acc2)
    }
    Pi(impl, name, in_term, out_term, _) -> {
      let acc1 = list.append(acc, impl)
      let acc2 = [name, ..acc1]
      let acc3 = collect_names_from_term_acc(in_term, acc2)
      collect_names_from_term_acc(out_term, acc3)
    }
    App(fun, implicit, arg, _) -> {
      let acc1 = collect_names_from_term_acc(fun, acc)
      let acc2 = collect_names_from_terms_acc(implicit, acc1)
      collect_names_from_term_acc(arg, acc2)
    }
    Match(arg, motive, cases, _) -> {
      let acc1 = collect_names_from_term_acc(arg, acc)
      let acc2 = collect_names_from_term_acc(motive, acc1)
      collect_names_from_cases_acc(cases, acc2)
    }
    Call(_, args, _) -> collect_names_from_terms_acc(args, acc)
    Comptime(term, _) -> collect_names_from_term_acc(term, acc)
    Fix(name, body, _) -> collect_names_from_term_acc(body, [name, ..acc])
  }
}

fn collect_names_from_terms_acc(
  terms: List(Term),
  acc: List(String),
) -> List(String) {
  case terms {
    [] -> acc
    [term, ..rest] -> {
      let acc1 = collect_names_from_term_acc(term, acc)
      collect_names_from_terms_acc(rest, acc1)
    }
  }
}

fn collect_names_from_cases_acc(
  cases: List(Case),
  acc: List(String),
) -> List(String) {
  case cases {
    [] -> acc
    [c, ..rest] -> {
      let acc1 = collect_names_from_term_acc(c.body, acc)
      collect_names_from_cases_acc(rest, acc1)
    }
  }
}

fn collect_names_from_fields_acc(
  fields: List(#(String, Term)),
  acc: List(String),
) -> List(String) {
  case fields {
    [] -> acc
    [#(_, term), ..rest] -> {
      let acc1 = collect_names_from_term_acc(term, acc)
      collect_names_from_fields_acc(rest, acc1)
    }
  }
}

/// Generalize holes by replacing them with fresh implicit type variables.
/// Returns: #(new_implicit_names, generalized_domain, generalized_codomain)
///
/// KEY FIX: Accept Value for both domain and codomain to properly substitute
/// holes in nested lambda types. The codomain is quoted to Term after substitution.
///
/// IMPORTANT: The domain is ALWAYS substituted, even if there are no holes to
/// generalize. This ensures the domain hole is replaced with an HVar.
fn generalize_holes(
  holes: List(Int),
  existing_implicit: List(String),
  domain: Value,
  codomain: Value,
  s: State,
  ffi: FFI,
  lvl: Int,
  span: Span,
) -> #(List(String), Value, Term) {
  // Create substitution: hole_id -> type variable (as a neutral term with HVar)
  // The index is the position in the new implicit list
  let base_index = list.length(existing_implicit)
  let hole_subst = create_hole_to_var_subst(holes, base_index)

  // ALWAYS substitute holes in domain, even if holes list is empty
  // This ensures the domain hole is replaced with an HVar
  let generalized_domain = subst_value_with_hole_vars(hole_subst, domain)

  case holes {
    [] -> #(
      existing_implicit,
      generalized_domain,
      quote(ffi, lvl, codomain, span),
    )
    _ -> {
      // Collect all existing names to avoid shadowing
      let codomain_term = quote(ffi, lvl, codomain, span)
      let existing_names =
        collect_existing_names(existing_implicit, codomain_term)

      // Generate unique names for each hole
      let new_names =
        generate_unique_names(list.length(holes), existing_names, 0)

      // Apply substitution to codomain (Value)
      let generalized_codomain_val =
        subst_value_with_hole_vars(hole_subst, codomain)
      let generalized_codomain = quote(ffi, lvl, generalized_codomain_val, span)

      // Return generalized domain (with holes substituted) and generalized codomain
      #(
        list.append(existing_implicit, new_names),
        generalized_domain,
        generalized_codomain,
      )
    }
  }
}

/// Generate unique names like _0, _1, _2, ... that don't conflict with existing names.
fn generate_unique_names(
  n: Int,
  existing: List(String),
  counter: Int,
) -> List(String) {
  case n <= 0 {
    True -> []
    False -> {
      let name = "_" <> int.to_string(counter)
      case list.contains(existing, name) {
        True -> generate_unique_names(n, existing, counter + 1)
        False -> [name, ..generate_unique_names(n - 1, existing, counter + 1)]
      }
    }
  }
}

/// Create substitution mapping hole IDs to De Bruijn indices for new type variables.
fn create_hole_to_var_subst(
  holes: List(Int),
  base_index: Int,
) -> List(#(Int, Int)) {
  create_hole_to_var_subst_loop(holes, base_index, [])
}

fn create_hole_to_var_subst_loop(
  holes: List(Int),
  index: Int,
  acc: List(#(Int, Int)),
) -> List(#(Int, Int)) {
  case holes {
    [] -> list.reverse(acc)
    [hole, ..rest] ->
      create_hole_to_var_subst_loop(rest, index + 1, [#(hole, index), ..acc])
  }
}

/// Substitute holes with type variables (as HVar) in a Value.
fn subst_value_with_hole_vars(subst: List(#(Int, Int)), value: Value) -> Value {
  case value {
    VNeut(HHole(id), []) -> {
      case list.key_find(subst, id) {
        Ok(index) -> VNeut(HVar(index), [])
        Error(Nil) -> value
      }
    }
    VNeut(HHole(id), spine) -> {
      case list.key_find(subst, id) {
        Ok(index) ->
          VNeut(
            HVar(index),
            list.map(spine, subst_elim_with_hole_vars(subst, _)),
          )
        Error(Nil) ->
          VNeut(HHole(id), list.map(spine, subst_elim_with_hole_vars(subst, _)))
      }
    }
    VNeut(HStepLimit, spine) ->
      VNeut(HStepLimit, list.map(spine, subst_elim_with_hole_vars(subst, _)))
    VNeut(head, spine) ->
      VNeut(head, list.map(spine, subst_elim_with_hole_vars(subst, _)))
    VRcd(fields) ->
      VRcd(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_hole_vars(subst, kv.1))
        }),
      )
    VCtrValue(VCtr(tag, arg)) ->
      VCtrValue(VCtr(tag, subst_value_with_hole_vars(subst, arg)))
    VLam(impl, name, env, body) ->
      VLam(impl, name, env, subst_term_with_hole_vars(subst, body))
    VPi(impl, name, env, in_val, out) ->
      VPi(
        impl,
        name,
        env,
        subst_value_with_hole_vars(subst, in_val),
        subst_term_with_hole_vars(subst, out),
      )
    VCall(name, args) ->
      VCall(name, list.map(args, subst_value_with_hole_vars(subst, _)))
    VFix(name, env, body) ->
      VFix(name, env, subst_term_with_hole_vars(subst, body))
    VRecord(fields) ->
      VRecord(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_hole_vars(subst, kv.1))
        }),
      )
    _ -> value
  }
}

/// Substitute holes with type variables in an elimination.
fn subst_elim_with_hole_vars(subst: List(#(Int, Int)), elim: Elim) -> Elim {
  case elim {
    EDot(name) -> EDot(name)
    EApp(arg) -> EApp(subst_value_with_hole_vars(subst, arg))
    EAppImplicit(arg) -> EAppImplicit(subst_value_with_hole_vars(subst, arg))
    EMatch(env, motive, cases) ->
      EMatch(env, subst_value_with_hole_vars(subst, motive), cases)
  }
}

/// Substitute holes with type variables (as Var) in a Term.
fn subst_term_with_hole_vars(subst: List(#(Int, Int)), term: Term) -> Term {
  case term {
    Hole(id, span) -> {
      case list.key_find(subst, id) {
        Ok(index) -> Var(index, span)
        Error(Nil) -> Hole(id, span)
      }
    }
    App(fun, impl, arg, span) ->
      App(
        subst_term_with_hole_vars(subst, fun),
        list.map(impl, subst_term_with_hole_vars(subst, _)),
        subst_term_with_hole_vars(subst, arg),
        span,
      )
    Pi(impl, name, in_t, out_t, span) ->
      Pi(
        impl,
        name,
        subst_term_with_hole_vars(subst, in_t),
        subst_term_with_hole_vars(subst, out_t),
        span,
      )
    Lam(impl, param, body, span) ->
      Lam(impl, param, subst_term_with_hole_vars(subst, body), span)
    Match(arg, motive, cases, span) ->
      Match(
        subst_term_with_hole_vars(subst, arg),
        subst_term_with_hole_vars(subst, motive),
        list.map(cases, subst_case_with_hole_vars(subst, _)),
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(kv) {
          #(kv.0, subst_term_with_hole_vars(subst, kv.1))
        }),
        span,
      )
    Ctr(tag, arg, span) -> Ctr(tag, subst_term_with_hole_vars(subst, arg), span)
    Dot(arg, name, span) ->
      Dot(subst_term_with_hole_vars(subst, arg), name, span)
    Ann(t, ty, span) ->
      Ann(
        subst_term_with_hole_vars(subst, t),
        subst_term_with_hole_vars(subst, ty),
        span,
      )
    Call(name, args, span) ->
      Call(name, list.map(args, subst_term_with_hole_vars(subst, _)), span)
    Comptime(t, span) -> Comptime(subst_term_with_hole_vars(subst, t), span)
    Fix(name, body, span) ->
      Fix(name, subst_term_with_hole_vars(subst, body), span)
    _ -> term
  }
}

/// Substitute holes in a Case.
fn subst_case_with_hole_vars(subst: List(#(Int, Int)), case_val: Case) -> Case {
  Case(
    case_val.pattern,
    subst_term_with_hole_vars(subst, case_val.body),
    option.map(case_val.guard, subst_term_with_hole_vars(subst, _)),
    case_val.span,
  )
}

/// Instantiate implicit type parameters with fresh holes.
/// Returns a substitution list mapping implicit param indices to hole IDs.
fn instantiate_implicit_params(
  implicit_params: List(String),
  s: State,
) -> #(List(#(Int, Int)), State) {
  instantiate_implicit_params_loop(implicit_params, 0, [], s)
}

fn instantiate_implicit_params_loop(
  params: List(String),
  index: Int,
  acc: List(#(Int, Int)),
  s: State,
) -> #(List(#(Int, Int)), State) {
  case params {
    [] -> #(list.reverse(acc), s)
    [_, ..rest] -> {
      let #(hole_val, s) = new_hole(s)
      // Extract hole ID from the value
      let hole_id = case hole_val {
        VNeut(HHole(id), []) -> id
        _ -> 0
        // Should not happen
      }
      instantiate_implicit_params_loop(
        rest,
        index + 1,
        [#(index, hole_id), ..acc],
        s,
      )
    }
  }
}

// ============================================================================
// HVAR SHIFTING FOR NESTED LAMBDAS
// ============================================================================

/// Shift HVar indices in a Value by a given offset.
/// Used when embedding a nested lambda's type in an outer context.
fn shift_hvar_in_value(value: Value, offset: Int) -> Value {
  case value {
    VNeut(HVar(level), []) -> VNeut(HVar(level + offset), [])
    VNeut(HVar(level), spine) ->
      VNeut(
        HVar(level + offset),
        list.map(spine, shift_hvar_in_elim(offset, _)),
      )
    VNeut(head, spine) ->
      VNeut(head, list.map(spine, shift_hvar_in_elim(offset, _)))
    VPi(implicit, name, env, in_val, out_term) ->
      VPi(
        implicit,
        name,
        list.map(env, shift_hvar_in_value(_, offset)),
        shift_hvar_in_value(in_val, offset),
        shift_hvar_in_term(out_term, offset),
      )
    VLam(implicit, name, env, body) ->
      VLam(
        implicit,
        name,
        list.map(env, shift_hvar_in_value(_, offset)),
        shift_hvar_in_term(body, offset),
      )
    VRcd(fields) ->
      VRcd(
        list.map(fields, fn(kv) { #(kv.0, shift_hvar_in_value(kv.1, offset)) }),
      )
    VCtrValue(VCtr(tag, arg)) ->
      VCtrValue(VCtr(tag, shift_hvar_in_value(arg, offset)))
    VCall(name, args) ->
      VCall(name, list.map(args, shift_hvar_in_value(_, offset)))
    VFix(name, env, body) ->
      VFix(
        name,
        list.map(env, shift_hvar_in_value(_, offset)),
        shift_hvar_in_term(body, offset),
      )
    VRecord(fields) ->
      VRecord(
        list.map(fields, fn(kv) { #(kv.0, shift_hvar_in_value(kv.1, offset)) }),
      )
    VTyp(_) | VLit(_) | VLitT(_) | VErr | VUnit -> value
  }
}

/// Shift HVar indices in an elimination by a given offset.
fn shift_hvar_in_elim(offset: Int, elim: Elim) -> Elim {
  case elim {
    EDot(name) -> EDot(name)
    EApp(arg) -> EApp(shift_hvar_in_value(arg, offset))
    EAppImplicit(arg) -> EAppImplicit(shift_hvar_in_value(arg, offset))
    EMatch(env, motive, cases) ->
      EMatch(
        list.map(env, shift_hvar_in_value(_, offset)),
        shift_hvar_in_value(motive, offset),
        // motive is a Value, not Term
        list.map(cases, shift_hvar_in_case(offset, _)),
      )
  }
}

/// Shift HVar indices in a Term by a given offset.
fn shift_hvar_in_term(term: Term, offset: Int) -> Term {
  case term {
    Var(index, span) -> Var(index, span)
    // De Bruijn indices don't shift
    Hole(id, span) -> Hole(id, span)
    // Hole IDs don't shift
    Typ(k, span) -> Typ(k, span)
    Lit(k, span) -> Lit(k, span)
    LitT(k, span) -> LitT(k, span)
    Unit(span) -> Unit(span)
    Err(msg, span) -> Err(msg, span)
    Lam(implicit, param, body, span) ->
      Lam(implicit, param, shift_hvar_in_term(body, offset), span)
    Pi(implicit, name, in_term, out_term, span) ->
      Pi(
        implicit,
        name,
        shift_hvar_in_term(in_term, offset),
        shift_hvar_in_term(out_term, offset),
        span,
      )
    App(fun, impl, arg, span) ->
      App(
        shift_hvar_in_term(fun, offset),
        list.map(impl, shift_hvar_in_term(_, offset)),
        shift_hvar_in_term(arg, offset),
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(kv) { #(kv.0, shift_hvar_in_term(kv.1, offset)) }),
        span,
      )
    Dot(arg, name, span) -> Dot(shift_hvar_in_term(arg, offset), name, span)
    Ann(t, ty, span) ->
      Ann(shift_hvar_in_term(t, offset), shift_hvar_in_term(ty, offset), span)
    Call(name, args, span) ->
      Call(name, list.map(args, shift_hvar_in_term(_, offset)), span)
    Comptime(t, span) -> Comptime(shift_hvar_in_term(t, offset), span)
    Fix(name, body, span) -> Fix(name, shift_hvar_in_term(body, offset), span)
    Ctr(tag, arg, span) -> Ctr(tag, shift_hvar_in_term(arg, offset), span)
    Match(arg, motive, cases, span) ->
      Match(
        shift_hvar_in_term(arg, offset),
        shift_hvar_in_term(motive, offset),
        list.map(cases, shift_hvar_in_case_term(offset, _)),
        span,
      )
  }
}

/// Shift HVar indices in a Case by a given offset.
fn shift_hvar_in_case(offset: Int, case_val: Case) -> Case {
  Case(
    case_val.pattern,
    // Patterns don't have HVar
    shift_hvar_in_term(case_val.body, offset),
    option.map(case_val.guard, fn(g) { shift_hvar_in_term(g, offset) }),
    case_val.span,
  )
}

/// Shift HVar indices in a Case (Term version) by a given offset.
fn shift_hvar_in_case_term(offset: Int, case_val: Case) -> Case {
  Case(
    case_val.pattern,
    shift_hvar_in_term(case_val.body, offset),
    option.map(case_val.guard, fn(g) { shift_hvar_in_term(g, offset) }),
    case_val.span,
  )
}

/// Substitute implicit type variables (HVar) with holes in a Value.
fn subst_value_with_implicit_vars(
  subst: List(#(Int, Int)),
  value: Value,
) -> Value {
  case value {
    VNeut(HVar(index), []) -> {
      case list.key_find(subst, index) {
        Ok(hole_id) -> VNeut(HHole(hole_id), [])
        Error(Nil) -> value
      }
    }
    VNeut(HVar(index), spine) -> {
      case list.key_find(subst, index) {
        Ok(hole_id) ->
          VNeut(
            HHole(hole_id),
            list.map(spine, subst_elim_with_implicit_vars(subst, _)),
          )
        Error(Nil) ->
          VNeut(
            HVar(index),
            list.map(spine, subst_elim_with_implicit_vars(subst, _)),
          )
      }
    }
    VNeut(HStepLimit, spine) ->
      VNeut(
        HStepLimit,
        list.map(spine, subst_elim_with_implicit_vars(subst, _)),
      )
    VNeut(head, spine) ->
      VNeut(head, list.map(spine, subst_elim_with_implicit_vars(subst, _)))
    VRcd(fields) ->
      VRcd(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_implicit_vars(subst, kv.1))
        }),
      )
    VCtrValue(VCtr(tag, arg)) ->
      VCtrValue(VCtr(tag, subst_value_with_implicit_vars(subst, arg)))
    VLam(impl, name, env, body) ->
      VLam(impl, name, env, subst_term_with_implicit_vars(subst, body))
    VPi(impl, name, env, in_val, out) ->
      VPi(
        impl,
        name,
        env,
        subst_value_with_implicit_vars(subst, in_val),
        subst_term_with_implicit_vars(subst, out),
      )
    VCall(name, args) ->
      VCall(name, list.map(args, subst_value_with_implicit_vars(subst, _)))
    VFix(name, env, body) ->
      VFix(name, env, subst_term_with_implicit_vars(subst, body))
    VRecord(fields) ->
      VRecord(
        list.map(fields, fn(kv) {
          #(kv.0, subst_value_with_implicit_vars(subst, kv.1))
        }),
      )
    _ -> value
  }
}

/// Substitute implicit type variables in an elimination.
fn subst_elim_with_implicit_vars(subst: List(#(Int, Int)), elim: Elim) -> Elim {
  case elim {
    EDot(name) -> EDot(name)
    EApp(arg) -> EApp(subst_value_with_implicit_vars(subst, arg))
    EAppImplicit(arg) ->
      EAppImplicit(subst_value_with_implicit_vars(subst, arg))
    EMatch(env, motive, cases) ->
      EMatch(env, subst_value_with_implicit_vars(subst, motive), cases)
  }
}

/// Substitute implicit type variables (Var) in a Term.
fn subst_term_with_implicit_vars(subst: List(#(Int, Int)), term: Term) -> Term {
  case term {
    Var(index, span) -> {
      // Check if this Var refers to an implicit type variable
      // Implicit type variables are at indices 0..n where n is the number of implicit params
      case list.key_find(subst, index) {
        Ok(hole_id) -> Hole(hole_id, span)
        Error(Nil) -> term
      }
    }
    App(fun, impl, arg, span) ->
      App(
        subst_term_with_implicit_vars(subst, fun),
        list.map(impl, subst_term_with_implicit_vars(subst, _)),
        subst_term_with_implicit_vars(subst, arg),
        span,
      )
    Pi(impl, name, in_t, out_t, span) ->
      Pi(
        impl,
        name,
        subst_term_with_implicit_vars(subst, in_t),
        subst_term_with_implicit_vars(subst, out_t),
        span,
      )
    Lam(impl, param, body, span) ->
      Lam(impl, param, subst_term_with_implicit_vars(subst, body), span)
    Match(arg, motive, cases, span) ->
      Match(
        subst_term_with_implicit_vars(subst, arg),
        subst_term_with_implicit_vars(subst, motive),
        list.map(cases, subst_case_with_implicit_vars(subst, _)),
        span,
      )
    Rcd(fields, span) ->
      Rcd(
        list.map(fields, fn(kv) {
          #(kv.0, subst_term_with_implicit_vars(subst, kv.1))
        }),
        span,
      )
    Ctr(tag, arg, span) ->
      Ctr(tag, subst_term_with_implicit_vars(subst, arg), span)
    Dot(arg, name, span) ->
      Dot(subst_term_with_implicit_vars(subst, arg), name, span)
    Ann(t, ty, span) ->
      Ann(
        subst_term_with_implicit_vars(subst, t),
        subst_term_with_implicit_vars(subst, ty),
        span,
      )
    Call(name, args, span) ->
      Call(name, list.map(args, subst_term_with_implicit_vars(subst, _)), span)
    Comptime(t, span) -> Comptime(subst_term_with_implicit_vars(subst, t), span)
    Fix(name, body, span) ->
      Fix(name, subst_term_with_implicit_vars(subst, body), span)
    _ -> term
  }
}

/// Substitute implicit type variables in a Case.
fn subst_case_with_implicit_vars(
  subst: List(#(Int, Int)),
  case_val: Case,
) -> Case {
  Case(
    case_val.pattern,
    subst_term_with_implicit_vars(subst, case_val.body),
    option.map(case_val.guard, subst_term_with_implicit_vars(subst, _)),
    case_val.span,
  )
}

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
    VNeut(HStepLimit, spine) -> list.any(spine, occurs_elim(sub, id, _))
    VNeut(_, spine) -> list.any(spine, occurs_elim(sub, id, _))
    VRcd(fields) -> list.any(fields, fn(kv) { occurs(sub, id, kv.1) })
    VCtrValue(VCtr(_, arg)) -> occurs(sub, id, arg)
    VUnit -> False
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
        Error(Nil) -> {
          // Check if we're unifying the hole with itself (already equal)
          case v2 {
            VNeut(HHole(id2), []) if id == id2 -> Ok(s)
            // Same hole, already unified
            VNeut(HStepLimit, _) -> Ok(s)
            // Step limit - don't unify further
            _ -> {
              // Check if the hole occurs in v2
              // (we already handled the case where v2 is the same hole above)
              case occurs(s.sub, id, v2) {
                True -> Error(InfiniteType(id, v2, s1, s2))
                False -> Ok(State(..s, sub: [#(id, v2), ..s.sub]))
              }
            }
          }
        }
      }
    _, VNeut(HHole(_), []) -> unify(s, v2, v1, s2, s1)
    VNeut(HStepLimit, _), VNeut(HStepLimit, _) -> Ok(s)
    // Both step limits are equal
    VNeut(h1, spine1), VNeut(h2, spine2) if h1 == h2 ->
      unify_elim_list(s, spine1, spine2, s1, s2)
    VRcd(fields1), VRcd(fields2) -> unify_fields(s, fields1, fields2, s1, s2)
    VCtrValue(VCtr(k1, arg1)), VCtrValue(VCtr(k2, arg2)) if k1 == k2 ->
      unify(s, arg1, arg2, s1, s2)
    VUnit, VUnit -> Ok(s)
    VLam(_, _, env1, body1), VLam(_, _, env2, body2) -> {
      // Unify lambdas by applying both to a fresh variable
      let #(fresh, s) = new_var(s)
      let a = eval(s.ffi, [fresh, ..env1], body1)
      let b = eval(s.ffi, [fresh, ..env2], body2)
      unify(s, a, b, s1, s2)
    }
    VPi(implicit1, _, env1, in1, out1), VPi(implicit2, _, env2, in2, out2) -> {
      // Unify Pi types by comparing domains and codomains
      // State is threaded through both unifications to preserve hole solutions
      case implicit1, implicit2 {
        [], [] -> {
          // No implicit params - unify domains and codomains directly
          // State is threaded through to preserve hole solutions from domain unification
          use s <- result.try(unify(s, in1, in2, s1, s2))
          let #(fresh, s) = new_var(s)
          let a = eval(s.ffi, [fresh, ..env1], out1)
          let b = eval(s.ffi, [fresh, ..env2], out2)
          unify(s, a, b, s1, s2)
        }
        _, _ -> {
          // Instantiate implicit params with fresh holes on both sides
          // This allows unifying generalized lambdas with expected types containing holes
          let #(subst1, s) = instantiate_implicit_params(implicit1, s)
          let #(subst2, s) = instantiate_implicit_params(implicit2, s)

          // Apply substitution to domains and codomains
          let in1_inst = subst_value_with_implicit_vars(subst1, in1)
          let out1_inst = subst_term_with_implicit_vars(subst1, out1)
          let in2_inst = subst_value_with_implicit_vars(subst2, in2)
          let out2_inst = subst_term_with_implicit_vars(subst2, out2)

          // Unify Pi types: first domains, then codomains (thread state correctly)
          use s <- result.try(unify(s, in1_inst, in2_inst, s1, s2))
          let #(fresh, s) = new_var(s)
          let a = eval(s.ffi, [fresh, ..env1], out1_inst)
          let b = eval(s.ffi, [fresh, ..env2], out2_inst)
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
  case term {
    Typ(k, _) -> #(VTyp(k), VTyp(k + 1), s)
    Lit(k, _) -> #(VLit(k), typeof_lit(k), s)
    LitT(k, _) -> #(VLitT(k), VTyp(0), s)
    Var(i, _) ->
      case ctx_get(s.ctx, i) {
        Some(#(val, ty)) -> {
          // Force the type with the current substitution to solve any holes
          let forced_ty = force(s.ffi, s.sub, ty)
          #(val, forced_ty, s)
        }
        None -> infer_error(s, VarUndefined(i, get_span(term)))
      }
    Hole(id, _) -> {
      // Record unsolved hole as a warning for IDE feedback
      let #(ty, s) = new_hole(s)
      #(VNeut(HHole(id), []), ty, with_err(s, HoleUnsolved(id, get_span(term))))
    }
    Rcd(fields, _) -> {
      let #(fields_val, fields_ty, s) = infer_fields(s, fields)
      #(VRcd(fields_val), VRcd(fields_ty), s)
    }
    Ctr(tag, arg, _) ->
      case list.key_find(s.ctrs, tag) {
        Error(Nil) -> infer_error(s, CtrUndefined(tag, get_span(term)))
        Ok(ctr) -> {
          let #(params, ctr_arg_ty, ctr_ret_ty, s) = check_ctr_def(s, ctr)
          let #(_, arg_ty, s) = infer(s, arg)
          let #(_, s) =
            check_type(
              s,
              arg_ty,
              ctr_arg_ty,
              get_span(arg),
              get_span(ctr.arg_ty),
            )
          let #(params, s) =
            ctr_solve_params(s, ctr, params, tag, get_span(term))
          let env = list.append(params, get_env(s))
          let arg_val = eval(s.ffi, env, arg)
          let ret_ty_val = eval(s.ffi, env, ctr.ret_ty)
          #(VCtrValue(VCtr(tag, arg_val)), ret_ty_val, s)
        }
      }
    Unit(_) -> #(VUnit, VTyp(0), s)
    Dot(arg, name, _) -> {
      let #(arg_val, arg_ty, s) = infer(s, arg)
      let val = do_dot(s.ffi, arg_val, name, 0, 100_000)
      case arg_ty {
        VRcd(fields) ->
          case list.key_find(fields, name) {
            Ok(ty) -> #(val, ty, s)
            Error(Nil) -> {
              let s = with_err(s, DotFieldNotFound(name, fields, get_span(arg)))
              #(val, VErr, s)
            }
          }
        VErr -> #(val, VErr, s)
        _ -> #(val, VErr, with_err(s, DotOnNonCtr(arg_ty, name, get_span(arg))))
      }
    }
    Ann(term, term_ty, _) -> {
      // Type annotation: evaluate the annotation type and check the term against it.
      // Note: We eval (not infer) the annotation because it's already a type expression.
      // For Ctr("Bool", Unit), eval gives us VCtrValue(VCtr("Bool", VUnit)), which is the type Bool.
      let ty_val = eval(s.ffi, get_env(s), term_ty)
      let #(val, s) = check(s, term, ty_val, get_span(term_ty))
      #(val, ty_val, s)
    }
    Lam(implicit, param, body, span) -> {
      // Lambda type inference with generalization for holes.
      // 
      // Unified approach: eval(param.1) handles all cases:
      // - Hole(_, _) -> VNeut(HHole(id), []) (type to be inferred)
      // - LitT, Typ, etc. -> explicit type value
      // - Complex types with holes -> VCtr/VRcd with embedded holes
      //
      // Generalization only happens when holes are present in domain or codomain.
      let #(name, _) = param
      let env = get_env(s)
      let holes_before = s.hole
      
      // Step 1: Evaluate the type annotation
      // - Hole(_, _) means "infer this type" - create a fresh hole
      // - Explicit types are evaluated to their values
      let #(domain_val, s) = case param.1 {
        Hole(_, _) -> new_hole(s)
        _ -> #(eval(s.ffi, get_env(s), param.1), s)
      }
      let #(_fresh, s) = def_var(s, name, domain_val)
      
      // Step 2: Infer the body
      let #(body_val, body_ty, s) = infer(s, body)

      // Step 3: Collect free holes from both domain and codomain
      let domain_holes = free_holes_in_value(s.sub, domain_val)
      let codomain_holes = free_holes_in_value(s.sub, body_ty)
      let all_holes = list.unique(list.append(domain_holes, codomain_holes))

      // Filter to only holes created during this lambda's inference
      let holes_to_generalize =
        list.filter(all_holes, fn(id) { id >= holes_before })

      // Step 4: Conditional generalization based on whether holes exist
      let has_holes = list.length(holes_to_generalize) > 0
      let #(final_implicit, final_t1, final_t2_term) = case has_holes {
        True -> {
          // Quote codomain at level + 1 to account for the implicit parameter binder
          let quote_lvl = list.length(env) + 1
          generalize_holes(
            holes_to_generalize,
            implicit,
            domain_val,
            body_ty,
            s,
            s.ffi,
            quote_lvl,
            span,
          )
        }
        False -> #(
          implicit,
          domain_val,
          quote(s.ffi, list.length(env), body_ty, span),
        )
      }

      // Step 5: Calculate number of new implicit parameters
      let num_new_implicit = list.length(final_implicit) - list.length(implicit)

      // Step 6: Create value bindings for new implicit parameters
      let ext_s = case num_new_implicit > 0 {
        True -> {
          // Create hole bindings for each new implicit parameter
          // These go BEFORE the explicit parameter in the context
          let #(bindings, new_s) = list.fold(
            holes_to_generalize,
            #([], s),
            fn(acc, hole_id) {
              let #(acc_bindings, acc_s) = acc
              let hole_val = VNeut(HHole(hole_id), [])
              // Generate name like "_0", "_1", etc.
              let idx = list.length(acc_bindings)
              let binding = #("_" <> int.to_string(idx), #(hole_val, hole_val))
              #([binding, ..acc_bindings], acc_s)
            },
          )
          // Prepend new bindings to context (reverse to maintain order)
          State(..new_s, ctx: list.append(list.reverse(bindings), new_s.ctx))
        }
        False -> s
      }

      // Step 7: Shift body term and re-evaluate if implicit params were added
      let #(final_body_val, final_body_ty, final_s) = case num_new_implicit > 0 {
        True -> {
          // Shift body term by number of new implicit parameters
          let shifted_body = shift_term(body, num_new_implicit)
          // Re-evaluate in extended context
          infer(ext_s, shifted_body)
        }
        False -> #(body_val, body_ty, s)
      }
      let s = case num_new_implicit > 0 { True -> final_s False -> s }

      // Step 8: Quote the body at the correct level
      // Add 1 for the lambda's own binder (the parameter)
      let quote_lvl = list.length(env) + num_new_implicit + 1
      let body_quoted = quote(s.ffi, quote_lvl, final_body_val, get_span(body))

      // Step 9: Shift the codomain term for the outer context
      let final_t2_shifted = shift_hvar_in_term(final_t2_term, num_new_implicit)

      // Return the lambda value and its type (with shifted codomain)
      #(
        VLam(final_implicit, name, env, body_quoted),
        VPi(
          final_implicit,
          name,
          env,
          final_t1,
          final_t2_shifted,
        ),
        s,
      )
    }
    Pi(implicit, name, in_term, out_term, _) -> {
      let env = get_env(s)
      let #(in_val, _, s) = infer(s, in_term)
      let #(_, s) = def_var(s, name, in_val)
      let #(_, _, s) = infer(s, out_term)
      #(VPi(implicit, name, env, in_val, out_term), VTyp(0), s)
    }
    App(fun, implicit, arg, _) ->
      infer_app(s, fun, implicit, arg, get_span(term))
    Match(arg, motive, cases, _) ->
      infer_match(s, arg, motive, cases, get_span(term))
    Call(name, args, _) -> {
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
    Comptime(term, _) -> {
      // Comptime blocks are evaluated during elaboration
      // Execute with comptime_eval for permission checking
      let #(val, s1) = comptime_eval(s, term)
      // Quote the result back to a term and infer its type
      let quoted = quote(s1.ffi, 0, val, get_span(term))
      let #(val2, ty, s2) = infer(s1, quoted)
      #(val2, ty, s2)
    }
    Fix(name, body, span) -> {
      // Fixpoint: fix f -> body
      // The fixpoint allows f to be referenced in body with the same type as the fixpoint
      let env = get_env(s)

      // KEY FIX: Check if body is an annotation. If so, use the annotated type directly
      // instead of creating a hole. This avoids InfiniteType errors for annotated functions.
      case body {
        Ann(lam, ann_ty, _ann_span) -> {
          // Body has type annotation: evaluate the annotation and check the lambda
          let ann_ty_val = eval(s.ffi, env, ann_ty)
          // Add the fixpoint variable to the context with the annotated type
          let #(_fresh, s) = def_var(s, name, ann_ty_val)
          // Check the lambda against the annotated type
          let #(body_val, s) = check(s, lam, ann_ty_val, span)
          // Return the annotated type (don't infer/generalize)
          let fix_val = VFix(name, env, body)
          #(fix_val, ann_ty_val, s)
        }
        _ -> {
          // No annotation: create a hole and infer as usual
          let #(result_ty_hole, s) = new_hole(s)
          // Add the fixpoint variable to the context with the hole type
          let #(_fresh, s) = def_var(s, name, result_ty_hole)
          // Check the body against the hole type
          let #(body_val, s) = check(s, body, result_ty_hole, span)
          // Force the hole to get the solved type
          let solved_ty = force(s.ffi, s.sub, result_ty_hole)
          let fix_val = VFix(name, env, body)
          #(fix_val, solved_ty, s)
        }
      }
    }
    Err(_, _) -> #(VErr, VErr, s)
    // Error terms have error type
  }
}

// ============================================================================
// INFER HELPERS
// ============================================================================

/// Infer type for function application.
///
/// Handles both normal applications and hole expansion:
/// - VPi: Apply function to argument, return result type
/// - Hole: Expand hole to function type, unify, then apply
fn infer_app(
  s: State,
  fun: Term,
  implicit: List(Term),
  arg: Term,
  span: Span,
) -> #(Value, Type, State) {
  let #(fun_val, fun_ty, s) = infer(s, fun)
  case fun_ty {
    VPi(implicit_params, _, pi_env, domain, codomain) -> {
      // Instantiate implicit type variables with fresh holes
      let #(implicit_subst, s) = instantiate_implicit_params(implicit_params, s)

      // Apply substitution to domain and codomain
      let domain_instantiated =
        subst_value_with_implicit_vars(implicit_subst, domain)
      let codomain_instantiated =
        subst_term_with_implicit_vars(implicit_subst, codomain)

      // Check argument against instantiated domain
      let #(arg_val, s) = check(s, arg, domain_instantiated, get_span(fun))
      // Evaluate codomain with argument in environment
      let out_val = eval(s.ffi, [arg_val, ..pi_env], codomain_instantiated)
      let out_val_forced = force(s.ffi, s.sub, out_val)
      #(do_app(s.ffi, fun_val, arg_val, 0, 100_000), out_val_forced, s)
    }
    VNeut(HHole(hole_id), spine) -> {
      // Hole expansion: ?1 applied to arg means ?1 = (?2 -> ?3)
      // Spine elements are already-evaluated values, handled by do_app
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
          Hole(result_ty_hole_id, get_span(fun)),
        )
      // Unify the original hole with the expanded type
      case
        unify(
          s,
          VNeut(HHole(hole_id), []),
          fun_ty_expanded,
          get_span(fun),
          get_span(fun),
        )
      {
        Ok(s) -> {
          // Check the argument against the domain hole
          let #(arg_val, s) = check(s, arg, arg_ty_hole_val, get_span(arg))
          // Result type is the codomain hole (spine will be applied by do_app)
          let out_val = result_ty_hole_val
          #(do_app(s.ffi, fun_val, arg_val, 0, 100_000), out_val, s)
        }
        Error(_) -> {
          // Avoid adding duplicate error if fun_ty is already VErr
          case fun_ty {
            VErr -> #(VErr, VErr, s)
            _ -> #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
          }
        }
      }
    }
    VNeut(HStepLimit, _) -> {
      // Step limit exceeded - return error
      #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
    }
    _ -> {
      // Avoid adding duplicate error if fun_ty is already VErr
      case fun_ty {
        VErr -> #(VErr, VErr, s)
        _ -> #(VErr, VErr, with_err(s, NotAFunction(fun, fun_ty)))
      }
    }
  }
}


/// Infer type for match expression.
///
/// The motive type is (x : arg_ty) → Type, where x is the scrutinee.
/// Each case is checked against the branch type, and exhaustiveness is verified.
fn infer_match(
  s: State,
  arg: Term,
  motive: Term,
  cases: List(Case),
  span: Span,
) -> #(Value, Type, State) {
  let env = get_env(s)
  let #(arg_val, arg_ty, s) = infer(s, arg)

  // The motive type is (x : arg_ty) → Type, where x is the scrutinee
  // For hole motives (lambdas with hole bodies), evaluate directly to preserve the hole ID
  let #(motive_val, s) = case motive {
    Lam(_, _, Hole(_, _), _) -> {
      // Hole motive: evaluate directly to get the lambda with the hole
      let motive_val = eval(s.ffi, env, motive)
      #(motive_val, s)
    }
    _ -> {
      // Regular motive: check against the expected type
      let motive_ty = VPi([], "_", env, arg_ty, Typ(0, get_span(arg)))
      let #(motive_val, s) = check(s, motive, motive_ty, get_span(motive))
      #(motive_val, s)
    }
  }

  // Apply the motive to the scrutinee to get the result type
  let result_ty = do_app(s.ffi, motive_val, arg_val, 0, 100_000)

  case cases {
    [] -> {
      // No clauses - exhaustiveness error
      let s = with_err(s, MatchMissingCase(span, PAny))
      let exhaustiveness_errors = check_exhaustiveness(s, cases, span)
      let s = list.fold(exhaustiveness_errors, s, with_err)
      #(VErr, result_ty, s)
    }

    [first_case, ..rest_cases] -> {
      // Check if the result type is a hole (non-dependent match with hole motive)
      case result_ty {
        VNeut(HHole(hole_id), []) -> {
          // Hole motive: infer result type from first clause body via unification.
          //
          // The key insight: when we check the first body against branch_ty (which
          // contains the hole), unification solves the hole automatically.
          //
          // Force arg_ty to get any solved type from the substitution
          let forced_arg_ty = force(s.ffi, s.sub, arg_ty)

          // Step 1: Bind pattern variables
          let #(first_pat_val, s) =
            bind_pattern(
              s,
              first_case.pattern,
              forced_arg_ty,
              get_span(first_case.body),
              get_span(arg),
            )

          // Step 2: Check guard if present
          let s = case first_case.guard {
            Some(guard_term) -> {
              let #(_guard_val, _guard_ty, s) = infer(s, guard_term)
              s
            }
            None -> s
          }

          // Step 3: Compute branch type (contains the hole)
          // branch_ty = motive(first_pat_val) = ?R (the hole)
          let branch_ty = do_app(s.ffi, motive_val, first_pat_val, 0, 100_000)

          // Step 4: Check first body against branch_ty
          // This UNIFIES the hole with the body's inferred type.
          // After this, s.sub contains: hole_id ↦ body_type
          let #(first_body_val, s) =
            check(s, first_case.body, branch_ty, get_span(first_case.body))

          // Step 5: Force the result type through substitution to get the solved type.
          // The hole in result_ty is now bound in s.sub, so forcing it gives us the
          // actual result type inferred from the first clause body.
          let solved_result_ty = force(s.ffi, s.sub, result_ty)

          // Step 6: Check remaining clauses with the solved result type.
          // For non-dependent matches (hole motive), all branches have the same type.
          let s =
            list.fold(rest_cases, s, fn(s, c) {
              let #(pat_val, s) =
                bind_pattern(
                  s,
                  c.pattern,
                  forced_arg_ty,
                  get_span(c.body),
                  get_span(arg),
                )
              let s = case c.guard {
                Some(guard_term) -> {
                  let #(_guard_val, _guard_ty, s) = infer(s, guard_term)
                  s
                }
                None -> s
              }
              let #(_, s) = check(s, c.body, solved_result_ty, get_span(c.body))
              s
            })

          // Step 7: Exhaustiveness check
          let exhaustiveness_errors = check_exhaustiveness(s, cases, span)
          let s = list.fold(exhaustiveness_errors, s, with_err)

          // Step 8: Compute match value
          // For the runtime match, we still need the motive. Force it to get the
          // solved lambda (with hole in body replaced).
          let solved_motive_val = force(s.ffi, s.sub, motive_val)
          let match_val =
            do_match(s.ffi, env, arg_val, solved_motive_val, cases, 0, 100_000)

          // Filter out HoleUnsolved errors for holes that are now solved in the substitution.
          // The error was added prematurely when we first encountered the hole during
          // motive checking, but the hole was solved by unification when checking the
          // first clause body.
          let s =
            State(
              ..s,
              errors: list.filter(s.errors, fn(e) {
                case e {
                  HoleUnsolved(id, _) -> {
                    // Keep the error only if the hole is still unsolved
                    list.key_find(s.sub, id) == Error(Nil)
                  }
                  _ -> True
                }
              }),
            )

          #(match_val, solved_result_ty, s)
        }

        VNeut(HStepLimit, _) -> {
          // Step limit exceeded - return error
          #(VErr, result_ty, with_err(s, NotAFunction(motive, result_ty)))
        }

        _ -> {
          // Concrete motive: use as-is (dependent or explicit non-dependent match)
          // Force arg_ty to get any solved type from the substitution
          let forced_arg_ty = force(s.ffi, s.sub, arg_ty)
          let s =
            list.fold(cases, s, fn(s, c) {
              let #(pat_val, s) =
                bind_pattern(
                  s,
                  c.pattern,
                  forced_arg_ty,
                  get_span(c.body),
                  get_span(arg),
                )
              let branch_ty = do_app(s.ffi, motive_val, pat_val, 0, 100_000)
              let s = case c.guard {
                Some(guard_term) -> {
                  let #(_guard_val, _guard_ty, s) = infer(s, guard_term)
                  s
                }
                None -> s
              }
              let #(_, s) = check(s, c.body, branch_ty, get_span(c.body))
              s
            })

          // Exhaustiveness check
          let exhaustiveness_errors = check_exhaustiveness(s, cases, span)
          let s = list.fold(exhaustiveness_errors, s, with_err)

          // Compute match value
          let match_val =
            do_match(s.ffi, env, arg_val, motive_val, cases, 0, 100_000)

          #(match_val, result_ty, s)
        }
      }
    }
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
    PTyp(k) -> check(s, Typ(k, pat_span), ret_ty, ret_span)
    PLit(k) -> check(s, Lit(k, pat_span), ret_ty, ret_span)
    PLitT(k) -> check(s, LitT(k, pat_span), ret_ty, ret_span)
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
            check_type(s, ctr_ret_ty, ret_ty, get_span(ctr.ret_ty), ret_span)
          let #(params, s) = ctr_solve_params(s, ctr, params, tag, pat_span)
          let env = list.append(params, get_env(s))
          let ctr_arg_ty = eval(s.ffi, env, ctr.arg_ty)
          let #(varg, s) =
            bind_pattern(s, parg, ctr_arg_ty, pat_span, get_span(ctr.arg_ty))
          #(VCtrValue(VCtr(tag, varg)), s)
        }
      }
    }
    PUnit -> #(VUnit, s)
  }
}

/// Check that a term has the expected type (verification direction).
///
/// Returns the evaluated value and updated state.
///
/// ERROR HANDLING: On error, records the error in state and returns VErr,
/// allowing checking to continue. This is how error recovery is implemented.
///
/// Simple implementation: infer the type and unify with expected type.
/// The infer function handles generalization for lambdas automatically.
///
/// SPECIAL CASE: For Fix with expected type, use the expected type directly
/// to avoid InfiniteType errors in recursive functions.
pub fn check(
  s: State,
  term: Term,
  expected_ty: Type,
  ty_span: Span,
) -> #(Value, State) {
  case term {
    Fix(name, body, span) -> {
      // Fixpoint with expected type: use the expected type instead of creating a hole
      // This avoids the InfiniteType error for recursive functions
      let env = get_env(s)
      // Add the fixpoint variable to the context with the expected type
      let #(_fresh, s) = def_var(s, name, expected_ty)
      // Check the body against the expected type
      let #(body_val, s) = check(s, body, expected_ty, span)
      let fix_val = VFix(name, env, body)
      #(fix_val, s)
    }
    Lam(implicit, param, body, span) -> {
      // Lambda with expected VPi type: use the domain type from the VPi
      case expected_ty {
        VPi(exp_implicit, exp_name, pi_env, domain, codomain) -> {
          // Use the domain type from the expected VPi
          let #(_fresh, s) = def_var(s, param.0, domain)
          // Check the body against the codomain (which is a Term, need to evaluate)
          let codomain_val = eval(s.ffi, get_env(s), codomain)
          let #(body_val, s) = check(s, body, codomain_val, span)
          let lam_val = VLam(implicit, param.0, get_env(s), body)
          #(lam_val, s)
        }
        _ -> {
          // No expected VPi type: infer and unify as usual
          let #(value, inferred_ty, s) = infer(s, term)
          // Avoid adding duplicate error if either type is already VErr
          case inferred_ty, expected_ty {
            VErr, _ | _, VErr -> #(VErr, s)
            _, _ -> {
              case unify(s, inferred_ty, expected_ty, get_span(term), ty_span) {
                Ok(s) -> #(force(s.ffi, s.sub, value), s)
                Error(e) -> #(VErr, with_err(s, e))
              }
            }
          }
        }
      }
    }
    _ -> {
      // For other terms, infer and unify as usual
      let #(value, inferred_ty, s) = infer(s, term)
      // Avoid adding duplicate error if either type is already VErr
      case inferred_ty, expected_ty {
        VErr, _ | _, VErr -> #(VErr, s)
        _, _ -> {
          case unify(s, inferred_ty, expected_ty, get_span(term), ty_span) {
            Ok(s) -> #(force(s.ffi, s.sub, value), s)
            Error(e) -> #(VErr, with_err(s, e))
          }
        }
      }
    }
  }
}

/// Process a constructor definition for type checking.
///
/// Creates holes for each type parameter and infers the argument and
/// return types in the extended context. Returns the parameter hole IDs
/// and the inferred types.
///
/// KEY FIX: For constructor definitions like CtrDef(["a"], Var(0), Typ(0)),
/// the Var(0) references the type parameter. After creating the hole for
/// the parameter, we substitute the hole value into the arg_ty and ret_ty.
fn check_ctr_def(s: State, ctr: CtrDef) -> #(List(Int), Value, Value, State) {
  let #(params, s) =
    list.fold(ctr.params, #([], s), fn(acc, name) {
      let #(params, s) = acc
      let id = s.hole
      let #(hole, s) = new_hole(s)
      let params = [id, ..params]
      // The type parameter should have the hole as both its value and type
      // This allows the type to be unified with the actual type later
      let s = State(..s, ctx: [#(name, #(hole, hole)), ..s.ctx])
      #(params, s)
    })

  // Substitute parameter holes into arg_ty and ret_ty
  // For Var(n) that references a parameter, replace with the hole value
  let arg_ty = subst_param_vars(ctr.arg_ty, params, s)
  let ret_ty = subst_param_vars(ctr.ret_ty, params, s)

  #(params, arg_ty, ret_ty, s)
}

/// Substitute parameter variables with their hole values.
/// Var(n) where n < length(params) is replaced with the corresponding hole.
fn subst_param_vars(term: Term, params: List(Int), s: State) -> Value {
  case term {
    Var(index, _) -> {
      // Look up the hole for this parameter index
      case get_param_hole(params, index, s) {
        Some(hole) -> hole
        None -> VErr
      }
    }
    Typ(k, _) -> VTyp(k)
    Lit(k, _) -> VLit(k)
    LitT(k, _) -> VLitT(k)
    Hole(id, _) -> VNeut(HHole(id), [])
    _ -> VErr
  }
}

/// Get the hole value for a parameter at the given index.
fn get_param_hole(params: List(Int), index: Int, s: State) -> Option(Value) {
  case list_get(params, index) {
    Some(id) -> {
      // Look up the hole in the substitution (it might already be solved)
      case list.key_find(s.sub, id) {
        Ok(val) -> Some(val)
        Error(Nil) -> Some(VNeut(HHole(id), []))
      }
    }
    None -> None
  }
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
///
/// For structured values (records, constructors, calls, etc.), we recurse
/// into their Value components to replace any holes they contain.
/// Note: VLam, VPi, VFix have Term bodies, not Value bodies, so they
/// are not recursed into here. The terms will be forced when evaluated.
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
    VNeut(HStepLimit, spine) ->
      VNeut(
        HStepLimit,
        list.map(spine, fn(elim) { force_elim(ffi, sub, elim) }),
      )
    VNeut(h, spine) ->
      VNeut(h, list.map(spine, fn(elim) { force_elim(ffi, sub, elim) }))
    VLam(_, _, _, _) -> value
    // Body is a Term, not a Value
    VPi(implicit1, name1, env1, in_val, out) -> {
      // in_val is Value, out is Term
      VPi(implicit1, name1, env1, force(ffi, sub, in_val), out)
    }
    VRcd(fields) -> {
      VRcd(list.map(fields, fn(kv) { #(kv.0, force(ffi, sub, kv.1)) }))
    }
    VCtrValue(VCtr(tag, arg)) -> {
      VCtrValue(VCtr(tag, force(ffi, sub, arg)))
    }
    VCall(name, args) -> {
      VCall(name, list.map(args, fn(a) { force(ffi, sub, a) }))
    }
    VFix(_, _, _) -> value
    // Body is a Term, not a Value
    VRecord(fields) -> {
      VRecord(list.map(fields, fn(kv) { #(kv.0, force(ffi, sub, kv.1)) }))
    }
    // These are already in normal form
    VTyp(_) | VLit(_) | VLitT(_) | VUnit | VErr -> value
  }
}

/// Force an elimination (spine element).
fn force_elim(ffi: FFI, sub: Subst, elim: Elim) -> Elim {
  case elim {
    EDot(field) -> EDot(field)
    EApp(arg) -> EApp(force(ffi, sub, arg))
    EAppImplicit(arg) -> EAppImplicit(force(ffi, sub, arg))
    EMatch(env, motive, cases) -> EMatch(env, motive, cases)
    // motive is Term
  }
}

/// Apply a spine (list of eliminations) to a value.
///
/// This is used when forcing metavariables that have pending operations.
fn apply_spine(ffi: FFI, value: Value, spine: List(Elim)) -> Value {
  apply_spine_loop(ffi, value, spine, 0, 100_000)
}

fn apply_spine_loop(
  ffi: FFI,
  value: Value,
  spine: List(Elim),
  steps: Int,
  max_steps: Int,
) -> Value {
  list.fold(spine, value, fn(value, elim) {
    case elim {
      EDot(field) -> do_dot(ffi, value, field, steps + 1, max_steps)
      EApp(arg) -> do_app(ffi, value, arg, steps + 1, max_steps)
      EAppImplicit(_) -> value
      // Implicit args are erased at runtime
      EMatch(env, motive, cases) ->
        do_match(ffi, env, value, motive, cases, steps + 1, max_steps)
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
    PUnit -> #(HCtr("Unit"), [])
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
    HCtr("Unit") -> PUnit
    _ -> PAny
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

/// Get the type family for a constructor.
fn get_type_family(s: State, tag: String) -> String {
  case list.key_find(s.ctrs, tag) {
    Ok(ctr) -> {
      case ctr.ret_ty {
        Typ(k, _) -> "typ_" <> int.to_string(k)
        // For App types like App(Var(1), [Var(0)], span), use the function part
        App(fun, _, _, _) -> {
          case fun {
            Var(i, _) -> "app_var_" <> int.to_string(i)
            _ -> "app"
          }
        }
        // For Ctr types like Ctr("T", Typ(1)), use the tag and arg type
        Ctr(type_tag, arg, _) -> {
          case arg {
            Typ(k, _) -> "ctr_" <> type_tag <> "_" <> int.to_string(k)
            _ -> "ctr_" <> type_tag
          }
        }
        _ -> "unknown"
      }
    }
    Error(Nil) -> "unknown"
  }
}

/// Find missing constructor heads for GADT-style exhaustiveness.
///
/// For constructor patterns, we check which other constructors of the
/// same type could apply but aren't covered. This handles GADTs where
/// Get the missing constructor heads for a type family.
///
/// Given the concrete heads already covered, return the heads that are missing.
/// For constructor types, returns all constructors of that type family not in concrete_heads.
/// For literal types, returns [HAny] since we can't enumerate all literal values.
/// For record types, returns empty (records are exhaustive).
///
/// Note: For prelude types (all returning Typ(0)), we use a hardcoded
/// mapping to group constructors by their type family:
/// - True, False -> Bool
/// - Some, None -> Option
/// - Ok, Err -> Result
/// - LT, EQ, GT -> Ordering
pub fn get_missing_heads(
  s: State,
  index: CtrIndex,
  concrete_heads: List(PHead),
) -> List(PHead) {
  case concrete_heads {
    [HAny, ..] -> []
    // Wildcard already covers everything
    [HCtr(name), ..] -> {
      let type_family = get_type_family(s, name)
      list.key_find(index, type_family)
      |> result.unwrap([])
      |> list.filter_map(fn(entry) {
        let #(tag, _) = entry
        Ok(HCtr(tag))
      })
      |> list.filter(fn(h) { !list.contains(concrete_heads, h) })
    }
    [HLit(_), ..] -> [HAny]
    // Literals: wildcard covers remaining values
    [HLitT(_), ..] -> [HAny]
    // Literal types: wildcard covers remaining values
    [HTyp(_), ..] -> [HAny]
    // Types: wildcard covers remaining types
    [HRcd(_), ..] -> []
    // Records are exhaustive
    [] -> [HAny]
    // No heads matched yet: wildcard covers everything
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
///   - If wildcard: check if matrix has wildcard (redundant if so)
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
          // Vector has wildcard. Check if matrix already has a wildcard.
          let matrix_has_wildcard =
            list.any(matrix, fn(row) {
              case row {
                [first_pattern, ..] -> {
                  case deconstruct(first_pattern).0 {
                    HAny -> True
                    _ -> False
                  }
                }
                [] -> False
              }
            })
          case matrix_has_wildcard {
            // Matrix has wildcard, so vector is redundant (no witnesses)
            True -> []
            // Matrix doesn't have wildcard, find missing constructors
            False -> {
              let concrete_heads = get_concrete_heads(matrix)
              let missing_heads = get_missing_heads(s, index, concrete_heads)
              list.flat_map(missing_heads, fn(missing) {
                let rest_witnesses =
                  useful(s, index, default_matrix(matrix), ps)
                list.map(rest_witnesses, fn(rest) {
                  let wildcards = list.repeat(PAny, head_arity(missing))
                  [reconstruct(missing, wildcards), ..rest]
                })
              })
            }
          }
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
  // If any clause has a guard, skip exhaustiveness checking
  // Guards add runtime conditions that the static checker cannot reason about
  let has_guard = list.any(cases, fn(c) { c.guard != None })
  case has_guard {
    True -> []
    // Skip exhaustiveness checking when guards are present
    False -> {
      // Check for redundant cases first
      let redundant_errors = check_redundant_cases(s, cases, span)

      // If the last case is a wildcard without a guard, the match is exhaustive
      case list.last(cases) {
        Ok(last_case) -> {
          case last_case.pattern {
            PAny -> {
              // PAny found - should be exhaustive
              redundant_errors
            }
            PAs(PAny, _) -> {
              // PAs(PAny, _) found - should be exhaustive
              redundant_errors
            }
            // Check for other patterns that should be exhaustive
            _ -> {
              // Not a recognized wildcard - continue with exhaustiveness checking
              let missing_errors = check_exhaustiveness_loop(s, cases, span)
              list.append(redundant_errors, missing_errors)
            }
          }
        }
        _ -> {
          // No cases - continue with normal exhaustiveness checking
          let missing_errors = check_exhaustiveness_loop(s, cases, span)
          list.append(redundant_errors, missing_errors)
        }
      }
    }
  }
}

/// Check for redundant cases in a match expression.
fn check_redundant_cases(
  s: State,
  cases: List(Case),
  match_span: Span,
) -> List(Error) {
  check_redundant_cases_loop(s, cases, [], [], match_span)
}

fn check_redundant_cases_loop(
  s: State,
  cases: List(Case),
  seen_patterns: List(Pattern),
  acc: List(Error),
  match_span: Span,
) -> List(Error) {
  case cases {
    [] -> list.reverse(acc)
    [case_, ..rest] -> {
      // Check if this pattern is redundant (already covered by seen patterns)
      let is_redundant =
        is_pattern_covered_by_list(s, case_.pattern, seen_patterns)
      let new_acc = case is_redundant {
        True -> [MatchRedundantCase(match_span), ..acc]
        False -> acc
      }
      check_redundant_cases_loop(
        s,
        rest,
        [case_.pattern, ..seen_patterns],
        new_acc,
        match_span,
      )
    }
  }
}

/// Check if a pattern is covered by a list of previously seen patterns.
fn is_pattern_covered_by_list(
  s: State,
  pattern: Pattern,
  seen: List(Pattern),
) -> Bool {
  // A pattern is covered if any seen pattern is more general
  list.any(seen, fn(seen_pattern) {
    is_pattern_covered_by(s, pattern, seen_pattern)
  })
}

/// Check if pattern1 is covered by pattern2 (pattern2 is more general).
fn is_pattern_covered_by(s: State, pattern1: Pattern, pattern2: Pattern) -> Bool {
  case pattern2 {
    PAny -> True
    // Wildcard covers everything
    PAs(PAny, _) -> True
    // As-pattern with wildcard covers everything
    PAs(inner, _) -> is_pattern_covered_by(s, pattern1, inner)
    _ -> False
    // Specific patterns don't cover other patterns
  }
}

fn check_exhaustiveness_loop(
  s: State,
  cases: List(Case),
  span: Span,
) -> List(Error) {
  // Build an index of constructors by their type family
  let index =
    list.fold(s.ctrs, [], fn(index, entry) {
      let #(tag, _) = entry
      let type_family = get_type_family(s, tag)
      let existing = list.key_find(index, type_family) |> result.unwrap([])
      list.key_set(index, type_family, [#(tag, entry.1), ..existing])
    })
  // Check each case for redundancy
  let #(matrix, redundant) =
    list.fold(cases, #([], []), fn(acc, c) {
      let #(matrix, diagnostics) = acc
      case useful(s, index, matrix, [c.pattern]) {
        [] -> #(matrix, [MatchRedundantCase(get_span(c.body)), ..diagnostics])
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
