# Core Language Specification

## Design Philosophy

Core is the **language-agnostic** dependent type theory implementation. It knows nothing about Tao, operators, or high-level syntax. It operates on:
- **De Bruijn indices** for syntax (`Term`)
- **De Bruijn levels** for semantics (`Value`)

### Naming Convention

All Core-level keywords, built-in types, and special constructs use the `$` prefix. FFI builtin functions use the `%` prefix:

| Category | Prefix | Examples |
|----------|--------|----------|
| Keywords | `$` | `$fn`, `$let`, `$match`, `$pi`, `$type`, `$error` |
| Built-in types | `$` | `$Int`, `$Float`, `$Type`, `$I32`, `$U64`, `$F64` |
| FFI functions | `%` | `%i32_add`, `%i32_to_f32`, `%u32_mul` |
| Constructors | `#` | `#Some`, `#True`, `#Nil`, `#Cons` |

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

### Example Tour Files (Source of Truth)

The tour directory is the source of truth for Core syntax:

```
examples/core/tour/
├── 01_basics/           # Basics: literals, records, type defs, constructors, lambdas, pi types, annotations, matches, builtin calls, holes, errors
├── 02_syntax_sugar/     # Sugar: let bindings, untyped lambda, untyped let, non-dependent pi
├── 03_literals/         # Numeric types: all integer sizes, float sizes, records
├── 04_type_definitions/ # Type defs: monomorphic, polymorphic, GADT vec, GADT expr
├── 05_pattern_matching/ # Patterns: wildcard, alias, type, int, record, record-type, ctr, error, guards, exhaustiveness
├── 06_builtins/         # FFI: i32, u32, i64, u64, f32, f64, conversions
└── 07_advanced/         # Advanced: default values, implicit params
```

## Type Definitions

### Numeric Types

Core supports a full hierarchy of numeric types. Type inference produces specific types, while patterns can match general wildcards.

```
$Int       — wildcard matching ANY integer type ($I8, $I16, $I32, $I64, $U8, $U16, $U32, $U64)
$Float     — wildcard matching ANY float type ($F16, $F32, $F64)
$I8, $I16, $I32, $I64   — signed integers (source: $I8 for 8-bit, etc.)
$U8, $U16, $U32, $U64   — unsigned integers (source: $U8 for 8-bit, etc.)
$F16, $F32, $F64       — floating point (source: $F16 for 16-bit, etc.)
```

**Examples from tour:**

```gleam
// Inference: 1 has no annotation, but type-checks against $I32
$let int: $I32 = 1;  // concrete type

// $Int matches any integer type in patterns
$match $Type { ... | $Int => 0 }  // $Int matches $I32, $U64, etc.

// Float literal accepts integer literals
$let float_int_lit: $Float = 42;
```

**Design rationale:** Integer literals are polymorphic over integer types. A literal `42` can have type `$I32`, `$U64`, or any integer type. Float literals can be `$Float` or any `$F*` type. The `$Int` and `$Float` wildcards match any member of their family in pattern matching.

### Literal Values

```gleam
/// Core literal value — the numeric value itself
pub type Literal {
  Int(value: Int)     // Generic integer value (source: 42, -1, 0, etc.)
  Float(value: Float) // Generic float value (source: 3.14, -0.5, etc.)
}
```

**Note:** During type checking, `Int` and `Float` values are unified against specific types (`$I32`, `$F64`, etc.). The `Literal` type remains simple; type specificity is handled by the type system, not the value type.

### Records

Core uses records for multiple purposes:

```
{x: 1, y: 2}        — record value
{field1: val1}      — single-field record
{}                  — empty record (Unit)
```

### Record Types with Defaults

Record types can specify default values for optional fields:

```
${x: $Int, y: $Int = 0}  — type with optional field y defaulting to 0
```

When a record value is checked against this type, missing fields are filled with defaults:

```
{x: 1}  :  ${x: $Int, y: $Int = 0}  — y is filled with 0
```

### Type Definitions (ADTs)

Type definitions use the `$type` keyword with constructor arrows:

```
$type {                                       // monomorphic type
| #True({}) -> #Bool({})
| #False({}) -> #Bool({})
}
```

```gleam
// Polymorphic type definition with type params
$let Option = $type<a: $Type> {
| #Some(a) -> #Option(a)
| #None({}) -> #Option(a)
}

// GADT-style type definition with multiple params (tour: 04_type_definitions/03_gadt_vec.core)
$let Vec = $type<n: $U32, a: $Type> {
  | #Nil({}) -> #Vec({n: 0, a: a})
  | #Cons({x: a, xs: #Vec({n: m, a: a})}) -> #Vec({n: %u32_add(m, 1) -> $U32, a: a})
}
```

Key features:
- **Monomorphic types**: No type parameters, defined directly with `$type { ... }`
- **Polymorphic types**: Use `$type<a: $Type, b: $Type> { ... }` syntax
- **GADT constraints**: Constructor arguments can be type patterns
- **Computed results**: Constructor result types can include FFI calls
- **@-bindings**: Constructor-bound variables use `@m` syntax for GADT unification

### Term (Syntax — De Bruijn Indices)

All Core terms use `$`-prefixed keywords in source. Keywords use De Bruijn indices for variables.

```gleam
/// Raw AST. Variables use De Bruijn indices (0 = closest binder above).
/// All terms carry source spans for error reporting.
pub type Term {
  Var(index: Int, span: Span)         // De Bruijn index variable
  Hole(id: Int, span: Span)           // Metavariable for inference
  Lam(implicits: List(#(String, Term)), param: #(String, Term), body: Term, span: Span)
  // Source: $fn<a: $Type>(x: a) => x  — implicits, param, body
  App(fun: Term, arg: Term, span: Span)
  // Source: ($fn(x: $Int) => x)(42)
  Pi(implicits: List(#(String, Term)), domain: #(String, Term), codomain: Term, span: Span)
  // Source: $pi(x: $Type) -> x  or  $pi<a: $Type>(a) -> a
  Lit(value: Literal, span: Span)     // Literal value (Int or Float)
  // Source: 42, 3.14
  Ctr(tag: String, arg: Term, span: Span)
  // Source: #Some(42), #True({}), #Cons({x: 42, xs: #Nil({})})
  Match(arg: Term, cases: List(Case), span: Span)
  // Source: $match arg { | pattern ? guard => body }
  Ann(term: Term, type_: Term, span: Span)
  // Source: 42 : $I32
  /// FFI builtin call: `%name(arg1: T1, arg2: T2, ...) -> ReturnType`
  /// `args` are (value, type) pairs for each argument.
  Call(name: String, args: List(#(Term, Term)), return_type: Term, span: Span)
  // Source: %i32_add(1: $I32, 2: $I32) -> $I32
  Rcd(fields: List(#(String, Term)), span: Span)
  // Source: {x: 1, y: 2}, {} (unit)
  Typ(level: Int, span: Span)         // Type universe $Type<n>
  // Source: $Type, $Type<0>, $Type<1>, $Type<x>
  TypeDef(name: String, params: List(#(String, Term)), constructors: List(#(String, List(String), Term, Term, Span)), span: Span)
  // Source: $type<a: $Type> { | #C(a) -> R }
  Err(message: String, span: Span)
  // Source: $error "my runtime error message"
}

/// Type of a Term: either a Value (evaluated) or Err
pub type Type = Value
```

### Source-to-Term Mapping

| Source Syntax | Term Constructor | Notes |
|--------------|-----------------|-------|
| `$fn(x: $Int) => body` | `Lam([], #(x, Int), body)` | No implicits |
| `$fn<a: $Type>(x: a) => body` | `Lam([(a, Type)], #(x, Var(0)), body)` | With implicits |
| `$let x: $Int = val` | `App(Lam([], #(x, Int), body), val)` | Body is implicit |
| `$match arg { | p => body }` | `Match(arg, [Case(p, None, body)])` |
| `arg : Type` | `Ann(arg, Type)` |
| `#Tag(arg)` | `Ctr("Tag", Rcd([("arg", arg)]))` | Args as record |
| `$error "msg"` | `Err("msg", span)` |
| `{x: 1, y: 2}` | `Rcd([("x", Lit(Int(1))), ("y", Lit(Int(2)))])` |
| `()` or `{}` | `Rcd([])` | Unit |
| `$Type<n>` | `Typ(n, span)` |
| `$type { | #C -> R }` | `TypeDef("name", [], [("C", [], self, result)])` | No params
| `$type<a: $Type> { | #C(a) -> R }` | `TypeDef("name", [("a", Type)], [("C", [], self, result)])` | With params

### Value (Semantics — De Bruijn Levels)

Fully evaluated results use De Bruijn levels (0 = innermost binder).

```gleam
/// Fully evaluated result. Variables use De Bruijn levels (0 = innermost binder).
pub type Value {
  VNeut(head: Head, spine: List(Elim))             // Neutral term (not a lambda)
  VLam(env: Env, implicits: List(#(String, Value)), param: #(String, Value), body: Term)      // Lambda value
  VPi(env: Env, implicits: List(#(String, Value)), domain: #(String, Value), codomain: Value)  // Pi type value
  VLit(value: Literal)                             // Evaluated literal
  VCtr(tag: String, arg: Value)                    // Constructor value
  VRcd(fields: List(#(String, Value)))             // Evaluated record
  VTypeDef(name: String, params: List(#(String, Value)), constructors: List(#(String, List(String), Value, Value, Span)))  // Type definition value
  /// Deferred FFI call — FFI returned None (not concrete enough), carry forward
  /// for runtime evaluation.
  VCall(name: String, args: List(#(Value, Value)), return_type: Value)  // Deferred FFI call
  VErr                                             // Error value
}

/// Neutral term head: variable or hole
pub type Head {
  HVar(level: Int)     // Variable at De Bruijn level
  HHole(id: Int)       // Unresolved hole
}

/// Neutral term spine: application, field access, match
pub type Elim {
  EApp(arg: Value)     // Apply to argument
  EDot(name: String)   // Field access (Phase 5+)
  EMatch(env: Env, motive: Value, cases: List(Case))  // Match elimination
}

/// A type alias for clarity
pub type Type = Value
```

### Value Examples

| Term | Value |
|------|-------|
| `42` | `VLit(Int(42))` |
| `$fn(x: $Int) => x` | `VLam([], #(x, VLit(Int(0))), body)` |
| `#Some(42)` | `VCtr("Some", VLit(Int(42)))` |
| `{x: 1, y: 2}` | `VRcd([("x", VLit(Int(1))), ("y", VLit(Int(2)))])` |
| `()` or `{}` | `VRcd([])` |
| `$error "msg"` | `VErr` |

### Patterns

Core supports 10+ pattern types:

```gleam
/// Patterns for pattern matching
pub type Pattern {
  PAny(span: Span)                  // Wildcard: _ (matches anything, no binding)
  PVar(name: String, span: Span)    // Variable: x (matches anything, binds name)
  PCtr(tag: String, arg: Pattern, span: Span)  // Constructor: #Some(x)
  PUnit(span: Span)                 // Unit: ()
  PLit(value: Literal, span: Span)  // Literal: 42
  PAs(pattern: Pattern, name: String, span: Span)  // Alias: x@pattern
  PType(universe: Option(Int), name: Option(String), span: Span)  // Type: $Type, $Type<1>, $Type<x>
  PRcd(fields: List(#(String, Pattern)), span: Span)  // Record: {x: 1, y: _}
  PRcdType(fields: List(#(String, Term, Option(Term))), span: Span)  // Record type: ${x: $Int}
  PErr(span: Span)                  // Error: $error
}

pub type Case {
  Case(pattern: Pattern, guard: Option(Term), body: Term, span: Span)
}
```

### Two-Stage Guards

Guards use a two-stage format that doesn't depend on boolean types:

```
| pattern ? expression ~ pass_pattern => body
```

1. Evaluate `expression` in scope of pattern bindings
2. Try to match result against `pass_pattern`
3. If match succeeds, execute body

```gleam
// Example from tour: 05_pattern_matching/09_guards.core
$match 42 {
| x ? x ~ 42 => 0   // succeeds: 42 matches 42
| _ => 1
}

// In a language with Bool:
// $match term {
// | x ? equals(x, 42) ~ #True(_) => 0
// | _ => 1
// }
```

### Environment Types

```gleam
/// Evaluation environment: list of values (De Bruijn levels)
pub type Env = List(Value)

/// Type checking context: variable name → (value, type)
pub type Context = List(#(String, #(Value, Type)))
```

### NbE-Driven Optimization

The type inference phase produces NbE-normalized values. This means the "value" returned from `infer()` is already in its minimal form:

```
Holes filled in → implicit arguments expanded → record defaults filled in →
comptime resolved → concrete beta reductions expanded → pattern matching resolved →
compile-time built-ins solved (constant folding)
```

Since types are fully resolved during type inference, overloaded function calls are resolved at the type inference stage — equivalent to comptime evaluation. The NbE result is both the checked term and its optimized value.

## Function Signatures

### infer.gleam — Bidirectional Type Checking

```gleam
/// Infer the type of a term (synthesis)
/// Returns: (result with holes and comptime resolved, inferred type, updated state)
pub fn infer(state: State, term: Term) -> #(Value, Value, State)

/// Check that a term has the expected type (verification)
/// Returns: (result with holes and comptime resolved, verified type, updated state)
pub fn check(state: State, term: Term, expected_type: Value) -> #(Value, Value, State)

/// Check a pattern against an expected type
/// Returns updated state with pattern bindings
pub fn check_pattern(state: State, pattern: Pattern, expected_type: Value) -> State

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
  TypeMismatch(expected: Value, got: Value, span: Span)       // Unified span
  VarUndefined(name: String, span: Span)
  HoleUnsolved(id: Int, span: Span)
  NotAFunction(fun_type: Value, span: Span)
  CtrUndefined(tag: String, span: Span)
  MatchMissing(patterns: List(String), covered: List(String), span: Span)
  MatchRedundant(span: Span)
  StepLimitExceeded(steps: Int, span: Span)
}
```

### state.gleam — Type Checker State

```gleam
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // Variable environment (name → #(value, type))
    errors: List(Error),       // Accumulated errors
    ffi: List(FfiEntry),       // FFI builtins
    hole_counter: Int,         // Next fresh hole ID
    truth_ctr: String,         // Name of truth constructor (e.g., "True") for guards
  )
}

/// FFI builtin definition — receives (value, type) pairs for overload resolution
pub type FfiEntry {
  FfiEntry(
    name: String,
    impl: fn(List(#(Value, Value))) -> Option(Value),  // (value, type) pairs for arguments
  )
}
```

**Key design:** `State` is a single, comprehensive record. Truth constructor defaults to `"True"` — configurable via `with_truth_ctr`. FFI entries receive `(value, type)` pairs for Phase 5+ operator overloading.

## Key Design Decisions

### 1. No Tao Assumptions in Core

Core knows NOTHING about:
- Tao-specific syntax (fn, let, import, type declarations)
- Tao operators (+, -, *, etc.)
- Tao language configuration
- Tao's module system

All Tao-specific behavior is in `tao/` and desugars to Core with `$`-prefixed syntax.

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

### 5. Holes Are Positive IDs Monotonically Increasing

```
Hole(0), Hole(1), Hole(2), ...
```

Hole IDs are monotonically increasing, managed by `hole_counter` in State.

### 6. Test-Driven Development

Every function in Core has tests that demonstrate:
- Happy path (correct input → correct output)
- Edge cases (empty lists, zero, single element)
- Error cases (type mismatches, undefined variables, etc.)
- Round-trip invariants (evaluate → quote → evaluate)

## Example: Core Terms

```gleam
// Identity function: $fn<a: $Type>(x: a) => x
Lam(
  implicits: [(a, Typ(0, span))],
  param: #(a, Var(0, span)),
  body: Var(0, span),
  span: span,
)
```

```gleam
// GADT-style type definition
TypeDef(
  name: "Expr",
  constructors: [
    #("LitInt", LitT(I32T), Var(0, span), span),
    #("LitBool", Ctr("Bool", Rcd([], span), span), Ctr("Bool", Rcd([], span), span), span),
  ],
  span: span,
)
```

```gleam
// Pattern match with type patterns and guards
Match(
  arg: Var(0, span),
  cases: [
    Case(PType(Some(1), None, span), None, Lit(Int(0), span), span),
    Case(PErr(span), None, Lit(Int(2), span), span),
  ],
  span: span,
)
```
