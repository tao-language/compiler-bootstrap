# Core Language Specification

A dependently typed core language with normalization by evaluation, bidirectional type checking, and integrated exhaustiveness checking.

---

## Table of Contents

1. [Overview](#overview)
2. [Core Concepts](#core-concepts)
3. [Syntax (Terms)](#syntax-terms)
4. [Semantics (Values)](#semantics-values)
5. [Type System](#type-system)
6. [Key Algorithms](#key-algorithms)
7. [Error Recovery](#error-recovery)
8. [API Reference](#api-reference)
9. [References](#references)
10. [Related Documentation](#related-documentation)

---

## Overview

This core language is designed as a **foundation for higher-level languages**. It provides:

- **Dependent Types**: Types can depend on values (e.g., `Vec(n, A)` where `n` is a runtime value)
- **Normalization by Evaluation (NbE)**: Efficient equality checking via evaluation + reification
- **Bidirectional Type Checking**: Synthesis (`infer`) and checking (`check`) modes for better inference
- **Exhaustiveness Checking**: Integrated static verification that pattern matches cover all cases (Maranget's algorithm)
- **Error Resilience**: Continues checking after errors to report all issues at once

### Design Principle

> **If there are no errors, the program is fully correct. If there are errors, we still check everything to report all issues in one pass.**

This is critical for IDE/LSP support where users need to see all errors, not just the first one.

### Error Handling Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  infer / check  (error-resilient)                           │
│  - Catches unify errors                                     │
│  - Records errors via with_err                              │
│  - Continues with VErr                                      │
│  - Runs exhaustiveness checking on Match                    │
└─────────────────────────────────────────────────────────────┘
                          ↓ calls
┌─────────────────────────────────────────────────────────────┐
│  unify  (NOT error-resilient)                               │
│  - Returns errors immediately on mismatch                   │
│  - Solves metavariables                                     │
│  - Checks occurs condition                                  │
└─────────────────────────────────────────────────────────────┘
```

---

## Core Concepts

### Syntax vs. Semantics

The language strictly separates **what you write** from **what it means**:

| Syntax (`Term`) | Semantics (`Value`) |
|-----------------|---------------------|
| Raw AST | Evaluated result |
| De Bruijn **Indices** | De Bruijn **Levels** |
| `Lam("x", body)` | `VLam("x", env, body)` (closure) |
| `Var(0)` | Look up index 0 in environment |

**Why?** Syntax is for parsing and printing. Semantics is for computation and equality checking.

### De Bruijn Indices vs. Levels

This is **critical** to understand. We use two different variable numbering schemes:

#### De Bruijn Indices (in `Term`)

Variables are numbered by **distance from their binder** (counting outward):

```
Term: λ. λ. Var(1)
      ↑  ↑    └─ Skip 1 binder (the inner λ), get the outer λ
      │  └─ Inner λ (binder 0)
      └─ Outer λ (binder 1 from inside)
```

**Problem**: If you move `Var(1)` into a deeper context, you must **shift** all indices.

#### De Bruijn Levels (in `Value` / `Head::HVar`)

Variables are numbered by **order of creation** (absolute from the top):

```
Value: λ. λ. HVar(0)
       ↑  ↑    └─ Always refers to the FIRST variable created
       │  └─ Level 1 (second variable)
       └─ Level 0 (first variable)
```

**Advantage**: Levels never need shifting. A level is stable no matter where you move it.

#### Conversion

When quoting a value back to syntax:
```
De Bruijn Index = Current Level - Variable Level - 1
```

Example: At level 5, quoting `HVar(2)`:
```
Index = 5 - 2 - 1 = 2
```

### Metavariables (`Hole`)

Metavariables are **unknowns to be solved** during type checking:

```gleam
Hole(id: Int)    // In syntax
HHole(id: Int)   // In semantics (neutral term)
```

When you write a function without a type annotation, the checker creates a hole, then **unifies** it with the actual type later.

**Example**:
```
Check: λx. x : ?0 → ?1
Unify: ?0 = A, ?1 = A
Result: λx. x : A → A
```

### Neutral Terms

A **neutral term** is a computation stuck on an unknown:

```gleam
VNeut(head, spine)
```

- `head`: Either a variable (`HVar`) or hole (`HHole`)
- `spine`: Pending operations (applications, projections, matches)

**Example**: If `x : A → B` is unknown, then `x y` is neutral:
```
VNeut(HVar(0), [EApp(v_y)])
```

Neutral terms allow checking to continue even when values are unknown.

---

## Syntax (Terms)

### Term Structure

Every term has a span for error reporting:
```gleam
Term(data: TermData, span: Span)
```

### Term Forms

| Constructor | Description | Example |
|-------------|-------------|---------|
| `Typ(k)` | Universe level k | `Type₀` |
| `Lit(v)` | Literal value | `42`, `3.14` |
| `LitT(t)` | Literal type | `I32`, `F64` |
| `Var(i)` | Bound variable (index) | `Var(0)` |
| `Hole(id)` | Metavariable | `?0` |
| `Rcd(fields)` | Record | `{x = 1, y = 2}` |
| `Ctr(tag, arg)` | Constructor | `Cons(1, Nil)` |
| `Dot(arg, field)` | Field projection | `r.x` |
| `Ann(term, typ)` | Type annotation | `(x : A)` |
| `Lam(name, body)` | Lambda | `λx. x` |
| `Pi(name, in, out)` | Dependent function | `(x : A) → B x` |
| `App(fun, arg)` | Application | `f x` |
| `Match(arg, motive, cases)` | Pattern match | `match x with ...` |

### Patterns

```gleam
PAny              // Wildcard: _
PAs(p, name)      // As-pattern: x @ pattern
PTyp(k)           // Type pattern: Typeₖ
PLit(v)           // Literal: 42
PLitT(t)          // Literal type: I32
PRcd(fields)      // Record: {x = p, y = q}
PCtr(tag, arg)    // Constructor: Cons(p)
```

---

## Semantics (Values)

### Value Forms

| Constructor | Description |
|-------------|-------------|
| `VTyp(k)` | Universe type |
| `VLit(v)` | Literal value |
| `VLitT(t)` | Literal type |
| `VNeut(head, spine)` | Neutral term |
| `VRcd(fields)` | Record value |
| `VCtr(tag, arg)` | Constructor value |
| `VLam(name, env, body)` | Closure (lambda) |
| `VPi(name, env, in, out)` | Dependent function type |
| `VErr` | Error (for recovery) |

### Closures

A closure captures its environment:

```gleam
VLam("x", env, body)
```

- `env`: Values of free variables when the lambda was created
- `body`: The term to evaluate (not yet evaluated)

**Why not evaluate immediately?** The argument isn't known until the function is called.

### Environments

```gleam
Env = List(Value)           // Runtime: index → value
Context = List(#(String, #(Value, Type)))  // Type checking: name → (value, type)
Subst = List(#(Int, Value)) // Unification: hole_id → solved value
```

---

## Type System

### Universes

Types are stratified into universe levels to avoid paradoxes:

```
Type₀ : Type₁ : Type₂ : ...
```

- `Typ(0)` is the type of small types (literals, data types)
- `Typ(1)` is the type of `Typ(0)` and large types
- And so on...

**Note**: Currently, universe levels must match exactly during unification. Cumulativity (using `Type₀` where `Type₁` is expected) is handled during type checking, not unification.

### Literal Types

```
42   : I32
3.14 : F64
I32  : Type₀
```

Literals have their specific types, and literal types live in `Type₀`.

### Dependent Function Types (Π-types)

```gleam
Pi("x", in_type, out_type)
```

The output type can depend on the input value:

```
(x : Nat) → Vec(x, A)  // Output type depends on x
```

When the output doesn't depend on the input, this is just a regular function:
```
A → B  ≡  (_ : A) → B
```

### Records

Records are first-class with labeled fields:

```
{x : I32, y : I64} : Type₀
```

Field order doesn't matter for equality (unification sorts by name).

### Constructors and GADTs

Constructors are defined with:

```gleam
CtrDef(
  params: List(String),  // Parameter names
  arg_ty: Term,          // Argument type
  ret_ty: Term           // Return type (can mention params)
)
```

**GADT Example**:
```gleam
// Nil : Vec(0, A)
CtrDef([], Unit, Vec(0, A))

// Cons : (n : Nat) → A → Vec(n+1, A)
CtrDef(["n"], A, Vec(Succ(n), A))
```

During type checking, constructor parameters are solved via unification.

---

## Key Algorithms

### Normalization by Evaluation (NbE)

To check if two terms are equal:

1. **Evaluate** both to values (compute everything possible)
2. **Quote** both back to terms (reify values to syntax)
3. **Compare** the quoted terms structurally

```gleam
normalize(env, term, span) = quote(length(env), eval(env, term), span)
```

**Why?** Direct syntactic comparison fails on equivalent terms:
```
(λx. x) y  ≠  y  (syntactically)
(λx. x) y  =  y  (after normalization)
```

### Evaluation (`eval`)

Evaluates a term in an environment:

```gleam
eval(env, term) -> Value
```

Key cases:
- `Var(i)`: Look up index `i` in `env`
- `Lam(name, body)`: Return `VLam(name, env, body)` (don't evaluate body yet)
- `App(fun, arg)`: Evaluate both, then apply:
  - If `fun` is `VLam`, substitute arg into body
  - If `fun` is neutral, return `VNeut(head, [EApp(arg), ...spine])`
- `Hole(id)`: Return `VNeut(HHole(id), [])` (neutral on unknown)

### Quoting (`quote`)

Converts a value back to syntax:

```gleam
quote(lvl, value, span) -> Term
```

Key cases:
- `VLam(name, env, body)`: 
  1. Create fresh neutral variable at `lvl`
  2. Evaluate body with this variable in env
  3. Quote the result at `lvl + 1`
  4. Return `Lam(name, quoted_body)`
- `VNeut(HVar(l), spine)`: Convert level to index: `Var(lvl - l - 1)`
- `VNeut(HHole(id), spine)`: Return `Hole(id)` with spine applications

### Unification (`unify`)

Solves metavariables by comparing values:

```gleam
unify(s, v1, v2, s1, s2) -> Result(State, Error)
```

Key cases:
- `VTyp(k1), VTyp(k2)`: Succeed if `k1 == k2`
- `VNeut(HHole(id), []), v2`: Solve hole `id = v2` (if no occurs violation)
- `VLam(_, env1, body1), VLam(_, env2, body2)`:
  1. Create fresh variable
  2. Evaluate both bodies with this variable
  3. Recursively unify results
- `VPi(...)`: Similar to lambdas, unify domains first, then codomains

**Occurs Check**: Prevents infinite types like `?0 = ?0 → ?0`

### Bidirectional Type Checking

Two modes that work together:

#### Inference (`infer`)

"Tell me the type of this term."

```gleam
infer(s, term) -> #(value, type, state)
```

Use for: variables, literals, applications, holes

#### Checking (`check`)

"Verify this term has the expected type."

```gleam
check(s, term, expected_ty, ty_span) -> #(value, state)
```

Use for: lambdas, constructors, annotations

**Why both?** Some constructs need top-down information:
- Lambda `λx. x` could have type `A → A` for any `A`
- Constructor `Nil` could be `Vec(0, A)` for any `A`

Checking provides the expected type from context.

### Pattern Matching (`bind_pattern`)

Binds variables from a pattern against a value:

```gleam
bind_pattern(s, pattern, ret_ty, pat_span, ret_span) -> #(value, state)
```

Returns the matched value and a state with new variables in context.

### Exhaustiveness Checking

The exhaustiveness checker uses **Maranget's matrix algorithm** to statically verify that pattern matches cover all possible cases. It's automatically called during type checking of `Match` expressions.

**Key Functions**:

```gleam
useful(s, index, matrix, vector) -> List(List(Pattern))
```

- `matrix`: Patterns already matched (the "coverage matrix")
- `vector`: New pattern to check
- `index`: Constructor index grouped by return type (for GADTs)
- Returns: List of **witnesses** (uncovered cases)

**Algorithm**:

| Result | Meaning |
|--------|---------|
| `[]` (empty) | Pattern is redundant (already covered) |
| `[witness, ...]` | These patterns are missing |

**Integration with Type Checking**:

```gleam
Match(arg, motive, cases) -> {
  // ... type check each case body ...
  
  // Run exhaustiveness checking
  let exhaustiveness_errors = check_exhaustiveness(s, cases, term.span)
  let s = list.fold(exhaustiveness_errors, s, with_err)
  
  // Continue with match evaluation
  ...
}
```

**Example**:
```gleam
-- Missing case
match b : Bool with
  True -> 1

-- Reports: MatchMissingCase(span, PCtr("False", PAny))

-- Redundant case  
match b : Bool with
  True -> 1
  True -> 2  -- Redundant!

-- Reports: MatchRedundantCase(span)
```

**GADT Support**:

For GADTs, the checker uses type unification to determine which constructors are possible:

```gleam
-- For Vec n A, if n = 0, only Nil is possible
match v : Vec(0, A) with
  Nil -> ...
  -- No Cons case needed (type system rules it out)
```

---

## Error Recovery

### Design Philosophy

> **Never stop checking because of an error.**

When an error occurs:
1. Record it in `state.errors`
2. Return `VErr` as the value/type
3. Continue checking

### Error Propagation

`VErr` propagates through evaluation:
```gleam
eval(env, App(VErr, arg)) = VErr
eval(env, Dot(VErr, "x")) = VErr
```

But checking continues:
```gleam
-- Even if `f` has an error, we still check `g`
(f : A → B) (g : C → D)
```

### Error Types

| Error | When |
|-------|------|
| `TypeMismatch(expected, got, ...)` | Types don't unify |
| `VarUndefined(index, span)` | Variable out of scope |
| `CtrUndefined(tag, span)` | Unknown constructor |
| `CtrUnsolvedParam(...)` | GADT parameter couldn't be solved |
| `HoleUnsolved(id, span)` | Metavariable recorded as unsolved (IDE warning) |
| `MatchRedundantCase(span)` | Unreachable pattern (covered by previous cases) |
| `MatchMissingCase(span, pattern)` | Missing pattern (exhaustiveness check) |
| `RcdMissingFields(names, span)` | Record missing fields |
| `DotFieldNotFound(name, ...)` | Field doesn't exist |
| `DotOnNonCtr(value, name, span)` | Projection on non-record |
| `InfiniteType(hole_id, ty, ...)` | Occurs check failure (infinite type) |
| `SpineMismatch(span1, span2)` | Incompatible spine elements (projection vs application) |
| `ArityMismatch(span1, span2)` | Different number of spine elements |
| `NotAFunction(fun, fun_ty)` | Application on non-function |
| `PatternMismatch(pattern, expected_ty, ...)` | Pattern doesn't match expected type |

**Note**: `MatchEmpty` was removed—empty matches now produce `MatchMissingCase(PAny)` via exhaustiveness checking.

### Collecting Nested Errors

Use `list_errors(value)` to extract errors hidden inside closures:

```gleam
list_errors(VLam("x", env, body))
-- Evaluates body in env to find nested errors
```

---

## API Reference

### Core Functions

```gleam
-- Evaluation
eval(env: Env, term: Term) -> Value
do_app(fun: Value, arg: Value) -> Value
do_match(env: Env, arg: Value, motive: Value, cases: List(Case)) -> Value
do_match_pattern(pattern: Pattern, value: Value) -> Result(Env, Nil)

-- Normalization by Evaluation
normalize(env: Env, term: Term, span: Span) -> Term
quote(lvl: Int, value: Value, span: Span) -> Term

-- Type Checking (bidirectional)
infer(s: State, term: Term) -> #(Value, Type, State)
  -- Returns: (value, type, state with accumulated errors)
  -- On error: records error, returns VErr, continues checking
check(s: State, term: Term, expected_ty: Value, ty_span: Span) -> #(Value, State)
  -- Returns: (value, state with accumulated errors)
  -- On error: records error, returns VErr, continues checking
unify(s: State, v1: Value, v2: Value, s1: Span, s2: Span) -> Result(State, Error)
  -- Returns: Error on mismatch (caught by infer/check)
  -- Solves metavariables, checks occurs condition

-- Pattern Matching
bind_pattern(s: State, pattern: Pattern, ret_ty: Value, ...) -> #(Value, State)
  -- Binds pattern variables to context during match type checking

-- Exhaustiveness Checking (Maranget's algorithm)
check_exhaustiveness(s: State, cases: List(Case), span: Span) -> List(Error)
  -- Returns: List of MatchRedundantCase and MatchMissingCase errors
  -- Called automatically by infer during Match type checking
useful(s: State, index: CtrIndex, matrix: PMatrix, vector: List(Pattern)) -> List(List(Pattern))
  -- Core algorithm: returns witnesses (uncovered cases)
specialize(matrix: PMatrix, target: PHead) -> PMatrix
  -- Specialize matrix for a constructor head
get_concrete_heads(matrix: PMatrix) -> List(PHead)
  -- Extract covered constructors from matrix
get_missing_heads(s: State, index: CtrIndex, concrete_heads: List(PHead)) -> List(PHead)
  -- Find missing constructors (handles GADTs)

-- Error Collection
list_errors(value: Value) -> List(Error)
  -- Extract errors from inside closures (for IDE feedback)
```

### State Management

```gleam
State(
  hole: Int,           -- Next fresh hole ID
  var: Int,            -- Next fresh variable level
  ctrs: CtrEnv,        -- Constructor definitions
  ctx: Context,        -- Typing context
  sub: Subst,          -- Metavariable solutions
  errors: List(Error), -- Accumulated errors
)
```

### Helper Functions

```gleam
new_hole(s: State) -> #(Value, State)      -- Create fresh metavariable
new_var(s: State) -> #(Value, State)       -- Create fresh variable
def_var(s: State, name: String, ty: Type) -> #(Value, State)  -- Add to context
force(sub: Subst, value: Value) -> Value   -- Resolve metavariables
with_err(s: State, err: Error) -> State    -- Add error to state
```

---

## Example Walkthrough

### Type Checking the Identity Function

Term: `λx. x`

Expected type: `?0 → ?1` (holes to be solved)

```
1. check(s, Lam("x", Var(0)), ?0 → ?1, span)
   
2. Create fresh variable for x:
   - x : ?2 (new hole)
   - ctx = [("x", (VNeut(HVar(0), []), ?2))]
   
3. Check body Var(0) against ?1:
   - infer(s, Var(0)) = (?2, ?2, s)  -- x has type ?2
   - unify(?2, ?1) → solve ?1 = ?2
   
4. Check domain:
   - unify(?0, ?2) → solve ?0 = ?2
   
5. Result:
   - Value: VLam("x", [], Var(0))
   - Type: VPi("x", [], ?2, ?2)  ≡  ?2 → ?2
   - Subst: [?0 = ?2, ?1 = ?2]
```

After forcing metavariables, the identity has type `A → A` for some `A`.

---

## Implementation Notes

### Why Records Sort Fields During Unification

```gleam
unify({a = 1, b = 2}, {b = 2, a = 1})  -- Should succeed!
```

Fields are sorted by name before comparison to ensure order-independence.

### Why Match Cases Store Terms, Not Values

```gleam
Case(pattern: Pattern, body: Term, span: Span)
```

The body is checked but not evaluated until the match executes. This allows:
- Type checking without committing to a branch
- Lazy evaluation of unreachable branches
- Proper error reporting in each branch

### Why `VPi` Stores `in: Value` but `out: Term`

```gleam
VPi(name: String, env: Env, in: Value, out: Term)
```

- `in` is evaluated because it's in negative position (contravariant)
- `out` is kept as a term because it may mention the bound variable

During quoting, both are handled correctly by extending the environment.

---

## For AI Assistants

When working with this codebase:

1. **Always distinguish** `Term` (syntax) from `Value` (semantics)
2. **Remember** De Bruijn indices (relative) vs. levels (absolute)
3. **Error recovery** is intentional—don't "fix" `VErr` propagation
4. **Metavariables** are solved by `unify`, forced by `force`
5. **Closures** capture environments—use `list_errors` to find nested issues
6. **Bidirectional typing**: `infer` for synthesis, `check` for verification

Key invariants:
- `eval` never modifies the environment (functional)
- `quote` is the inverse of `eval` (for normal forms)
- `unify` accumulates solutions in `State.sub`
- Errors are accumulated, never thrown

---

## References

This implementation is based on established research in type theory and programming language design:

### Normalization by Evaluation

- **Berger, U., & Schwichtenberg, H. (1991).** "An Inverse of the Evaluation Functional for Typed λ-Calculus." *LICS.*  
  Introduces normalization by evaluation—evaluating to a semantic domain then reifying back to syntax.

- **Danvy, O., & Filinski, A. (1992).** "Representing Methods, Partially." *Technical Report.*  
  Develops the partial evaluation perspective on NbE.

- **Abel, A., Coquand, T., & Dybjer, P. (2007).** "Normalization by Evaluation for Martin-Löf Type Theory with Typed Equality Judgements." *LICS.*  
  Extends NbE to dependent type theory with equality.

### Bidirectional Type Checking

- **Pierce, B. C., & Turner, D. N. (1998).** "Local Type Inference." *POPL.*  
  Foundational work on bidirectional typing for local type inference.

- **Pfenning, F. (2002).** "Structural Cut Elimination I. Intuitionistic and Linear Logic." *Information and Computation.*  
  Uses bidirectional techniques in proof theory.

- **Dunfield, J., & Krishnaswami, N. R. (2013).** "Complete and Easy Bidirectional Type Checking for Higher-Rank Polymorphism." *ICFP.*  
  Modern treatment with completeness proofs.

- **Löwe, A., & Stone, C. A. (2002).** "Bidirectional Type Checking for Dependent Types." *Unpublished.*  
  Early application to dependent types.

### Exhaustiveness Checking

- **Maranget, L. (2007).** "Warnings for Pattern Matching." *Journal of Functional Programming.*  
  The matrix algorithm used in this implementation.  
  [Available online](http://moscova.inria.fr/~maranget/papers/warn/index.html)

- **Garrigue, J., & Nagashima, Y. (2019).** "Exhaustive Pattern Matching for Records and Variants." *ML Family Workshop.*  
  Extensions to records and GADTs.

### De Bruijn Indices and Levels

- **de Bruijn, N. G. (1972).** "Lambda Calculus Notation with Nameless Dummies." *Indagationes Mathematicae.*  
  Original introduction of nameless variables.

- **McBride, C. (2002).** "De Bruijn Indices in Agda." *Unpublished notes.*  
  Explains the distinction between indices (syntax) and levels (semantics).

### Dependent Types and Metavariables

- **Martin-Löf, P. (1980).** "Intuitionistic Type Theory." *Bibliopolis.*  
  Foundational work on dependent type theory.

- **Coquand, T. (1996).** "From Semantics to Rules: A Machine Assisted Analysis." *Journal of Symbolic Logic.*  
  Relates semantic and syntactic approaches to type theory.

- **Goguen, H., McBride, C., & McKinna, J. (2006).** "Eliminating Dependent Pattern Matching." *Algebraic Methodology and Software Technology.*  
  Pattern matching in dependent type theory.

### Unification and Metavariables

- **Robinson, J. A. (1965).** "A Machine-Oriented Logic Based on the Resolution Principle." *JACM.*  
  Original unification algorithm.

- **Huet, G. P. (1975).** "A Unification Algorithm for Typed λ-Calculus." *Theoretical Computer Science.*  
  Higher-order unification.

- **Miller, D. (1991).** "A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification." *Journal of Logic and Computation.*  
  Pattern unification for metavariables.

### Error Recovery and IDE Support

- **Watt, S. M. (2008).** "Type Checking with Errors." *Unpublished.*  
  Discusses accumulating errors during type checking.

- **Eisenberg, R. A. (2016).** "Type-Directed Compilation of Row-Typed Polymorphic Records." *POPL.*  
  Error resilience in GHC.

### General Resources

- **The Agda Team.** "Agda Documentation."  
  [https://agda.readthedocs.io/](https://agda.readthedocs.io/)

- **The Idris Team.** "Idris Documentation."  
  [https://idris2.readthedocs.io/](https://idris2.readthedocs.io/)

- **The Lean Team.** "The Lean Theorem Prover."  
  [https://leanprover.github.io/](https://leanprover.github.io/)

- **Harper, R. (2016).** "Practical Foundations for Programming Languages." *Cambridge University Press.*  
  Comprehensive treatment of type systems.

- **Pierce, B. C. (2002).** "Types and Programming Languages." *MIT Press.*  
  Standard reference for type systems.

- **Nordström, B., Petersson, K., & Smith, J. M. (1990).** "Programming in Martin-Löf's Type Theory." *Oxford University Press.*
  Dependent types from a programming perspective.

---

## Related Documentation

### Parser and Formatter

- [`docs/parser-formatter.md`](parser-formatter.md) - Complete guide to the lexer, parser, and formatter
  - Token types and lexical rules
  - Parsing strategy and grammar
  - Formatting rules
  - Usage examples
  - API reference

### Implementation Files

- [`src/core.gleam`](../src/core.gleam) - Core language implementation (1400+ lines)
  - Type definitions (Term, Value, Pattern, etc.)
  - Evaluation and normalization
  - Unification and type checking
  - Exhaustiveness checking

- [`src/parser.gleam`](../src/parser.gleam) - Parser implementation (540+ lines)
  - Lexer (tokenization)
  - Recursive descent parser
  - Error handling

- [`src/formatter.gleam`](../src/formatter.gleam) - Formatter implementation (190+ lines)
  - Term formatting
  - Pattern formatting
  - Simple pretty-printing