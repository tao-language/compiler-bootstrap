# compiler_bootstrap

[![Package Version](https://img.shields.io/hexpm/v/compiler_bootstrap)](https://hex.pm/packages/compiler_bootstrap)
[![Hex Docs](https://img.shields.io/badge/hex-docs-ffaff3)](https://hexdocs.pm/compiler_bootstrap/)

```sh
gleam add compiler_bootstrap@1
```

```gleam
import compiler_bootstrap

pub fn main() -> Nil {
  // TODO: An example of the project in use
}
```

Further documentation can be found at <https://hexdocs.pm/compiler_bootstrap>.

## Development

```sh
gleam run   # Run the project
gleam test  # Run the tests
```

If you have `fswatch` installed, you can run tests as files change with:

```sh
fswatch -or src test | xargs -n1 -I{} gleam test
```

# Core Language Architecture

Welcome to the documentation for our dependently typed language core.

This document explains the foundational concepts, the architecture of the type checker and evaluator, and how all the core functions (`eval`, `quote`, `check`, `infer`, `unify`) work together. Whether you are a new contributor or just want to understand how a modern bidirectional type checker works under the hood, this guide is for you.

---

## 1. Core Concepts & Terminology

Before diving into the code, it's essential to understand the theoretical paradigms this system is built upon.

### Dependent Types

In standard programming languages, types and values are strictly separated (e.g., `String` is a type, `"hello"` is a value). In a **Dependently Typed** language, types are just first-class values. Types can depend on runtime values, and functions can compute types.

- **Example:** A standard list type `List(Int)` only knows it contains integers. A dependent vector type `Vec(2, Int)` knows it contains exactly _two_ integers. The type depends on the value `2`.

### Syntax vs. Semantics

Our compiler strictly separates the _blueprint_ of the code from the _execution_ of the code.

- **Syntax (`Term`)**: The raw Abstract Syntax Tree (AST) as written by the programmer or parsed from a file. It is "dumb" and unevaluated.
- **Semantics (`Value`)**: The evaluated, runtime representation of the code. Operations have been computed, and functions have been turned into active "Closures" that remember their environment.

### Normalization by Evaluation (NbE)

How do we check if two complex types are equal? We evaluate both of them to their simplest possible runtime form, and then read them back into syntax to compare them.

1. **Evaluate** a `Term` into a `Value`.
2. **Quote** the `Value` back into a simplified `Term`.
   This round-trip process is called **Normalization**.

### Bidirectional Type Checking

Instead of trying to guess (infer) the type of every single expression from the bottom up, we use two interacting modes:

1. **Infer**: "Look at this expression and tell me its type." (Used for variables, literals, and function applications).
2. **Check**: "I expect this expression to have _this_ exact type. Verify it." (Used for lambdas, constructors, and match branches).
   This allows us to omit redundant type annotations. If the checker knows we want a `Vec(2, Int)`, it pushes that expectation _down_ into the constructor, rather than making the constructor guess.

---

## 2. Tricky Concepts Explained

### Variables: De Bruijn Indices vs. De Bruijn Levels

Because names (like `x` or `y`) get confusing when functions are nested, compilers use numbers instead of names for variables. We use two different numbering systems depending on whether we are looking at Syntax (`Term`) or Semantics (`Value`).

#### De Bruijn Indices (Used in `Term`)

An index represents the **relative distance** from the variable to the function that bound it.

- _Code:_ `\x -> \y -> x`
- _With Indices:_ `\ -> \ -> Var(1)`
- _Explanation:_ To find the value for `Var(1)`, go up one binder (skip `y`) and find `x`.
- _The Catch:_ If you move `Var(1)` into a deeper nested function, its index has to shift to stay correct. This makes substitution annoying.

#### De Bruijn Levels (Used in `Value` inside `Head::HVar`)

A level represents the **absolute depth** from the top of the program. Variables are numbered in the exact order they are created.

- _Code:_ `\x -> \y -> x`
- _With Levels:_ `x` is `Level 0`. `y` is `Level 1`. The body is returning `Level 0`.
- _Explanation:_ No matter how deep you nest `Level 0`, it will always refer to the very first variable. This makes runtime environments incredibly fast and stable.

### Metavariables (`HMeta`)

When checking Generalized Algebraic Data Types (GADTs) or polymorphic constructors (like `Nil`), the compiler doesn't immediately know what the type parameters are.
We represent these "holes" as **Metavariables** (`HMeta(id)`). The type checker will use `unify` to solve these holes by comparing them against the expected type, generating a `Subst` (Substitution dictionary) of answers.

### Error Recovery (`WithErrors`)

Usually, if a type checker finds an error, it stops checking or replaces the type with a generic "Error" type, causing cascading errors down the line.
Our system uses a resilient `WithErrors(Value, List(Error))` wrapper. If you type `Cons("wrong_type", Nil)`, the compiler doesn't throw away the fact that it's a list. It returns `WithErrors(Vec(2, Int), [TypeMismatch...])`. This allows IDE features like auto-complete to keep working even when there is a typo inside the arguments!

---

## 3. Core Environments

To keep track of variables, we use three distinct lists:

- **`Env` (Runtime Environment)**: A `List(Value)`. Used during evaluation. It maps De Bruijn Indices to actual memory values.
- **`Context` (Typing Context)**: A `List(#(String, Value))`. Used during type checking. It maps variable names to their computed _Types_.
- **`TypeEnv` (Constructor Environment)**: A mapping of Constructor tags (like `"Cons"`) to their `CtrDef` signatures.

---

## 4. The Core Pipeline: How Functions Work

### `eval(env: Env, term: Term) -> Value`

Takes raw syntax and "runs" it within a given environment.

- Literals become values.
- Variables look up their data in the `Env`.
- Functions (`Lam`, `Pi`) become closures (`VLam`, `VPi`). They don't evaluate their bodies immediately; they save the current `Env` inside themselves for later.
- Function Application (`App`) triggers `eval_apply`, which pushes the argument into the closure's saved environment and evaluates the body.

### `quote(lvl: Int, value: Value, s: Span) -> Term`

The inverse of `eval`. It takes a runtime value and converts it back to syntax.

- _Why do we need `lvl`?_ When quoting a closure (`VLam`), we don't have a real argument to pass it. So, we create a "fake" variable using the current `lvl` (`VNeut(HVar(lvl))`), pass it to the closure, evaluate the body, and quote the result. It safely converts De Bruijn Levels back into De Bruijn Indices.

### `normalize(env: Env, term: Term, s: Span) -> Term`

Simply calls `eval` followed by `quote`. This reduces an expression to its absolute simplest form.

### `unify(lvl: Int, sub: Subst, v1: Value, v2: Value, s: Span) -> Result(Subst, Error)`

Checks if two `Value`s are mathematically equal.

- If it encounters identical structures (e.g., `VLit(I32(5))` and `VLit(I32(5))`), it succeeds.
- If it encounters an unsolved hole (`VNeut(HMeta(id))`), it **solves** it by adding the other value to the `Subst` dictionary.
- It threads this `Subst` through the comparison, ensuring all type parameters are solved consistently.

### `infer(lvl: Int, ctx: Context, env: Env, tenv: TypeEnv, term: Term) -> Value`

_Synthesizes_ the type of a term from the bottom up.

- If you ask it to infer a variable, it looks it up in the `Context`.
- If you ask it to infer an `App(f, x)`, it infers `f` to get a `Pi` type, checks that `x` matches the input type, and returns the output type.
- If you ask it to infer a Lambda or Constructor, it fails with `TypeAnnotationNeeded` because it doesn't have enough top-down information.

### `check(lvl: Int, ctx: Context, env: Env, tenv: TypeEnv, term: Term, expected_ty: Value) -> Value`

Verifies that a term matches a known, expected type.

- **Constructors (`check_ctr`)**: When checking a `Ctr`, it generates `HMeta`s for the constructor's parameters, unifies the expected type against the constructor's return type to solve those Metas, and then evaluates the constructor arguments in that newly solved environment.
- **Fall-through**: If it doesn't have a specific `check` rule for an AST node, it simply calls `infer` to get the term's synthesized type, and uses `unify` to prove that the synthesized type matches the `expected_ty`.

---

## 5. Future Work & Unimplemented Features

To make this a fully complete language core, the following systems need to be implemented or finalized:

1. **Exhaustiveness Checking (`Match` constraints):**

- Currently, `eval_match` will fail at runtime if a case is unhandled. The type checker (`infer` for `Match`) needs a reachability/exhaustiveness matrix to statically prove that all possible patterns are covered and return `NonExhaustiveMatch` if they aren't.

2. **Pattern Binding (`bind_pattern`):**

- The `bind_pattern` function has a `todo` for `PCtr`. It needs to recursively check constructor arguments, infer their types, and push all bound variables (`PVar`) into the typing `Context`.

3. **Metavariable Quoting (`quote`):**

- Quoting `VNeut(HMeta(id))` currently triggers a `todo`. It needs to look up the Meta in the substitution environment or render it as a hole (e.g., `?0`).

4. **Deep Error Surfacing (`list_errors`):**

- `list_errors` currently has `todo`s for closures (`VLam` and `VPi`). We need a way to peek inside closures to extract internal argument errors without triggering evaluation side effects.

5. **Parsing & Lexing:**

- A frontend parser is needed to convert raw string text into the `Term` AST.

6. **Module System:**

- A way to handle imports, top-level definitions, and maintaining a global `Context` and `TypeEnv` across multiple files.

## References

- **Local type inference (bidirectional typing)**: Pierce, B. C., & Turner, D. N. (2000)
- **Checking Dependent Types with Normalization by Evaluation**: Christiansen, D. R.
- **A tutorial implementation of a dependently typed lambda calculus**: Löh, A., McBride, C., & Swierstra, W. (2010).
- **Warnings for Pattern Matching**: Luc Maranget (2007)
- **Compiling Pattern Matching to Good Decision Trees**: Luc Maranget
