# Core Language Specification

## Design Philosophy

Core is the **language-agnostic** dependent type theory implementation. It knows nothing about Tao, operators, or high-level syntax. It operates on:
- **De Bruijn indices** for syntax (`Term`)
- **De Bruijn levels** for semantics (`Value`)

## Directory Structure

```
src/core/
├── ast.gleam              # Term, Value, Pattern, Head, Elim types
├── state.gleam            # Type-checker state, FFI, error types
├── infer.gleam            # Bidirectional type inference/checking
├── eval.gleam             # Normalization by evaluation
├── quote.gleam            # Value → Term
├── unify.gleam            # Higher-order unification
├── subst.gleam            # Substitution (levels → indices)
├── generalize.gleam       # Quantify holes to universal types
├── exhaustiveness.gleam   # Maranget-style pattern match checking
├── syntax.gleam           # Core parser + formatter (uses grammar lib)
├── error_formatter.gleam  # Type error diagnostics
├── ast_string.gleam       # Debug stringification
├── list_utils.gleam       # List helper functions
└── color.gleam            # ANSI color codes
```

## Type Definitions

### Literals

Literals are handled gracefully to support both explicit type annotations and inference:
- `(1 : I32)` is valid — integer literal with explicit I32 type
- `(1 : U64)` is valid — integer literal with explicit U64 type (integer literals are polymorphic over integer types)
- `(3.14 : I32)` is **an error** — float literal cannot coerce to integer type
- `(1 + 2)` with no annotation resolves to a concrete type based on context

```gleam
/// Core literal value — the numeric value itself
pub type LitValue {
  ILit(value: Int)     // Integer literal value (source: 42, -1, 0, etc.)
  FLit(value: Float)   // Float literal value (source: 3.14, -0.5, etc.)
  StrLit(value: String) // String literal value
}

/// Literal type — either concrete or generic during inference
pub type LitType {
  // Concrete types — specific bit-width and signedness
  I32T   // 32-bit signed integer
  I64T   // 64-bit signed integer
  U32T   // 32-bit unsigned integer
  U64T   // 64-bit unsigned integer
  F32T   // 32-bit float
  F64T   // 64-bit float
  
  // Generic types — used during inference when type is not yet resolved
  ILitT  // Generic integer literal type (unifies with I32T, I64T, U32T, U64T)
  FLitT  // Generic float literal type (unifies with F32T, F64T)
}
```

**Design rationale:** There is a single `ILit` literal value and a single `FLit` literal value (not per-type variants). The type system distinguishes between concrete types (`I32T`, `U64T`, etc.) and generic literal types (`ILitT`, `FLitT`). 

Checking a literal against a specific type validates compatibility: integer literals can unify with any integer type (`ILitT` ↔ `I32T`, `ILitT` ↔ `U64T`), but float literals cannot unify with integer types. When inferring on a generic numeric literal without context, the result is a generic literal type (`ILitT` or `FLitT`) which can later be unified with a more specific type from context. A float literal like `3.14` explicitly annotated as `: I32` is an error because `FLitT` does not unify with integer types.

### Term (Syntax — De Bruijn Indices)

```gleam
/// Raw AST. Variables use De Bruijn indices (0 = closest binder above).
/// All terms carry source spans for error reporting.
pub type Term {
  Typ(universe: Int, span: Span)      // Type universe (Type, Type@1, etc.)
  Lit(value: LitValue, span: Span)    // Literal value (ILit, FLit, StrLit)
  Var(index: Int, span: Span)         // De Bruijn index variable
  Hole(id: Int, span: Span)           // Metavariable for inference
  Err(message: String, span: Span)    // Error placeholder
  Lam(param: #(String, Term), body: Term, span: Span)  // Lambda
  App(fun: Term, arg: Term, span: Span)                  // Application
  Pi(domain: Term, codomain: Term, span: Span)          // Pi type (dependent function)
  LitT(typ: LitType, span: Span)                        // Literal type term (I32T, ILitT, etc.)
  Ctr(tag: String, arg: Term, span: Span)               // Constructor
  Rcd(fields: List(#(String, Term)), span: Span)        // Record
  Dot(record: Term, field: String, span: Span)          // Field access
  Ann(term: Term, typ: Term, span: Span)                // Type annotation
  Match(arg: Term, motive: Term, cases: List(Case), span: Span)  // Pattern match
  Call(name: String, args: List(#(Term, Term)), ret: Term, span: Span)  // FFI call
  Comptime(term: Term, span: Span)                      // Compile-time evaluation
  Fix(name: String, body: Term, span: Span)             // Recursion fixpoint
  Let(name: String, value: Term, body: Term, span: Span)  // Let binding
  Unit(span: Span)                                       // Unit value ()
}

/// Type of a Term: either a Value (evaluated) or Err
pub type Type = Value
```

### Value (Semantics — De Bruijn Levels)

```gleam
/// Fully evaluated result. Variables use De Bruijn levels (0 = innermost binder).
/// Uses neutral spine representation for efficient application.
pub type Value {
  VTyp(universe: Int)                              // Universe Type(n)
  VLit(value: LitValue)                            // Evaluated literal (ILit, FLit, StrLit)
  VLitT(typ: LitType)                              // Evaluated literal type (I32T, ILitT, etc.)
  VNeut(head: Head, spine: List(Elim))             // Neutral term (not a lambda)
  VRcd(fields: List(#(String, Value)))             // Evaluated record
  VLam(implicit: List(String), name: String, env: Env, body: Term)  // Lambda
  VPi(implicit: List(String), name: String, env: Env, in_val: Value, out_term: Term)  // Pi type
  VCtrValue(tag: String, arg: Value)               // Constructor value
  VUnit                                              // Unit value ()
  VCall(name: String, args: List(#(Value, Value)), ret: Value)  // FFI call result
  VFix(name: String, env: Env, body: Term)         // Recursion fixpoint
  VErr                                               // Error value
}

/// Neutral term head: variable, hole, or step limit
pub type Head {
  HVar(level: Int)
  HHole(id: Int)
  HStepLimit
}

/// Neutral term spine: field access, application, match
pub type Elim {
  EDot(name: String)
  EApp(arg: Value)
  EAppImplicit(value: Value)
  EMatch(env: Env, motive: Value, cases: List(Case))
}

/// A type alias for clarity
pub type Type = Value
```

### Pattern and Case

```gleam
/// Patterns for pattern matching
pub type Pattern {
  PAny(span: Span)
  PAs(pattern: Pattern, name: String, span: Span)
  PTyp(universe: Int, span: Span)
  PLit(value: Literal, span: Span)
  PLitT(typ: LitType, span: Span)
  PRcd(fields: List(#(String, Pattern)), span: Span)
  PCtr(tag: String, arg: Pattern, span: Span)
  PUnit(span: Span)
}

pub type Case {
  Case(pattern: Pattern, body: Term, guard: Option(Term), span: Span)
}
```

### Constructor Definitions (for Type Checking)

```gleam
/// Constructor definition from type declarations
pub type CtrDef {
  CtrDef(
    params: List(String),  // Type parameters
    arg_ty: Term,          // Argument type
    ret_ty: Term,          // Return type
  )
}

/// Constructor environment: maps constructor names to their definitions
pub type CtrEnv = List(#(String, CtrDef))
```

### Environment Types

```gleam
/// Evaluation environment: list of values (De Bruijn levels)
pub type Env = List(Value)

/// Type checking context: variable name → (value, type)
pub type Context = List(#(String, #(Value, Type)))
```

## Function Signatures

### infer.gleam — Bidirectional Type Checking

```gleam
/// Infer the type of a term (synthesis)
/// Returns: (term with holes resolved, inferred type, updated state)
pub fn infer(state: State, term: Term) -> #(Term, Value, State)

/// Check that a term has the expected type (verification)
/// Returns: (term with holes resolved, verified type, updated state)
pub fn check(state: State, term: Term, expected: Value) -> #(Term, Value, State)

/// Infer a pattern against an expected type
/// Returns updated state with pattern bindings
pub fn infer_pattern(state: State, pattern: Pattern, expected: Value) -> State

/// Check exhaustiveness of match cases
/// Returns updated state with any missing/redundant cases
pub fn check_exhaustiveness(
  state: State,
  scrutinee_type: Value,
  cases: List(Case),
) -> State
```

### eval.gleam — Normalization by Evaluation

```gleam
/// Evaluate a term to a value with FFI built-in on an environment
pub fn eval(ffi: List(FfiEntry), env: Env, term: Term) -> Value

/// Apply a value to an argument (part of neutral spine evaluation)
pub fn do_app(function: Value, arg: Value) -> Value
```

### quote.gleam — Value → Term

```gleam
/// Quote a value back to a term (re-wrapping lambdas)
/// DOES NOT call eval — quote is purely syntactic
pub fn quote(env: Env, value: Value) -> Term
```

### unify.gleam — Higher-Order Unification

```gleam
/// Unify two values, returning extended substitution
pub fn unify(state: State, expected: Value, actual: Value) -> State

/// Check if a value occurs in its own type (occurs check)
/// Returns False to allow recursive types
pub fn occurs(level: Int, value: Value) -> Bool
```

### subst.gleam — Substitution

```gleam
/// Force (evaluate) a value through the substitution
/// Converts HHole values to resolved values
pub fn force(ffi: List(FfiEntry), subst: Subst, value: Value) -> Value

/// Shift de Bruijn indices by delta
pub fn shift_term(term: Term, delta: Int) -> Term

/// Substitute level → index (value → term representation)
/// Critical for converting between eval and infer
pub fn force_levels_to_indices(subst: Subst, value: Value) -> Term
```

### generalize.gleam — Quantification

```gleam
/// Generalize a type by quantifying over free holes
/// Converts HHole(level) → ∀Hole(level)
pub fn generalize(state: State, value: Value) -> #(Value, State)
```

### exhaustiveness.gleam — Maranget's Algorithm

```gleam
/// Check if match cases are exhaustive for a given type
/// Returns state with any missing cases added as errors
pub fn check_exhaustiveness(
  state: State,
  scrutinee: Value,
  cases: List(Case),
) -> State

/// Check if a case is redundant given earlier cases
pub fn is_redundant(case: Case, earlier_cases: List(Case)) -> Bool
```

## Error Types

### state.gleam — Type Error Diagnostics

```gleam
pub type Error {
  TypeMismatch(expected: Value, got: Value, expected_span: Span, got_span: Span)
  VarUndefined(index: Int, span: Span)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(fun: Term, fun_type: Value, span: Span)
  ArityMismatch(expected: Int, actual: Int, fn_span: Span, call_span: Span)
  CtrUndefined(tag: String, span: Span)
  InfiniteType(hole_id: Int, ty: Value, self_span: Span, ctx_span: Span)
  RcdMissingFields(fields: List(String), span: Span)
  CtrUnsolvedParam(tag: String, id: Int, span: Span)
  DotFieldNotFound(name: String, available: List(String), span: Span)
  DotOnNonCtr(value: Value, name: String, span: Span)
  SpineMismatch(expected: Value, actual: Value, fn_span: Span, call_span: Span)
  PatternMismatch(pattern: Pattern, expected_type: Value, pattern_span: Span, value_span: Span)
  MatchMissingCase(span: Span, missing_pattern: String)
  MatchRedundantCase(span: Span)
  ComptimePermissionDenied(operation: String, required: List(String), span: Span)
  TODO(message: String)
  NameShadow(name: String, first_span: Span, second_span: Span)
  SyntaxError(span: Span, expected: String, got: String, context: String)
}
```

### state.gleam — Type Checker State

```gleam
pub type State {
  State(
    ctrs: CtrEnv,              // Constructor definitions
    truth_ctor: String,        // Truth constructor name ("True" or "true"), false is != true
    holes: List(#(Int, Value)),  // Unsolved holes: id → type
    subst: Subst,              // Unification substitutions
    errors: List(Error),       // Accumulated errors
    ffi: List(FfiEntry),       // FFI builtins
    step_limit: Int,           // Evaluation step limit
  )
}

/// FFI builtin definition — each FFI entry is a single concrete target, no overloads
pub type FfiEntry {
  FfiEntry(
    name: String,
    impl: fn(List(#(Value, Value))) -> Option(Value),  // (value, type) pairs for arguments
    ret_type: Value,          // Return type
  )
}
```

**Key change from current code:** `State` is now a single, comprehensive state record that contains everything. No scattered globals. FFI entries are passed through the state explicitly.

## Key Design Decisions

### 1. No Tao Assumptions in Core

Core knows NOTHING about:
- Tao-specific syntax (fn, let, import, type declarations)
- Tao operators (+, -, *, etc.)
- Tao language configuration
- Tao's module system

All Tao-specific behavior is in `tao/` and desugars to Core before type checking.

### 2. Explicit Error Accumulation

Every public function in Core returns `State` (which contains `errors: List(Error)`). There are no exceptions, no early returns, no `panic`. Errors accumulate and are reported at the end.

### 3. Neutral Spine for Efficiency

Values use a neutral spine representation (`VNeut(head, spine)`) for efficient application:
- `VNeut(HVar(0), [EApp(v1), EApp(v2)])` = `x v1 v2`
- `VNeut(HHole(5), [EDot("field")])` = `?5.field`
- `VNeut(..., [EMatch(...)])` = match expression

This avoids repeatedly allocating new `Value` records for each application.

### 4. Quote Does Not Evaluate

Quote transforms a `Value` back to `Term` by re-wrapping evaluated lambdas. It never calls `eval`. This is a critical invariant — if `quote` calls `eval`, you get exponential blowup (as discovered in the current codebase).

### 5. Holes Use Negative IDs for Synthesis

```
Hole(-1) → synthesized during infer (positive ID assigned during infer)
Hole(1)  → verified against during check (positive ID given by caller)
```

This allows the type checker to distinguish between:
- **Synthesis holes** (infer): "I don't know the type, figure it out"
- **Verification holes** (check): "I know the type is this, verify"

### 6. Test-Driven Development

Every function in Core has tests that demonstrate:
- Happy path (correct input → correct output)
- Edge cases (empty lists, zero, single element)
- Error cases (type mismatches, undefined variables, etc.)
- Round-trip invariants (evaluate → quote → evaluate)

## Example: Core Terms

```gleam
// Identity function: fn(x: a) -> a
/// Term.Pi(#("", Term.Var(0, ...), Term.Var(0, ...)))
Pi(
  domain: Var(0, span),    // param type: a (bound by pi)
  codomain: Var(0, span),  // return type: a (same binder)
)
```

```gleam
// Church numeral 2: λf.λx.f (f x)
/// Term.Lam(("f", Term.Lam(("x", Term.App(Var(1, span), Var(0, span))))))
Lam(
  param: ("f", Lam(("x", App(Var(1, span), Var(0, span))))),
  body: App(Var(1, span), Var(0, span)),
)
```

```gleam
// Pattern match on Maybe(a)
/// Term.Match(arg, motive, [Case(PCtr("Some", PAny()), body), Case(PCtr("None", Unit()), body)])
Match(
  arg: Var(0, span),
  motive: Ctr("Maybe", Hole(-1, span), span),
  cases: [
    Case(PCtr("Some", PAny(span)), body_some, None, span),
    Case(PCtr("None", Unit(span)), body_none, None, span),
  ],
)
```
