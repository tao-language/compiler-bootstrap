# Soundness

What the type checker guarantees, what it does not, and where the
deliberate approximations live. Read `implicit-args.md` for the
implicit-argument mechanism and `overloads.md` for overload dispatch;
this document is the single place for the *admitted* gaps.

## The guarantee

The checker is a bidirectional type checker over Core, implemented by
normalization by evaluation (`eval` → `quote`). The correctness
guarantee is one-way:

> **If `infer`/`check` report no errors, evaluation is correct.**

With errors present, evaluation is undefined behavior: `eval` is blind
(no type lookups, no module records, no error reporting), so a value
depends only on its term, and whatever it produces over an ill-typed
term is fine.

The machinery that makes the guarantee hold:

* **Occurs check** (`core/occurs`) in `solve_hole`: a hole meeting a
  solution that contains itself is an `InfiniteType` error, so the
  `For`-instantiation rule cannot manufacture non-well-founded types.
* **Three-valued pattern matching** (`core/eval`, `MatchResult`): a
  neutral field or tail *may still* match, so such matches are kept as
  `NMatch` and re-reduced via `unwrap` once the neutrals resolve,
  instead of baking in the wrong case or an `Err`.
* **De Bruijn discipline**: values address environment entries by
  *level* (stable under push/pop), terms by *index*, converted with
  `index = env_size − level − 1` and guarded by an assert in `quote`.
  `instantiate` re-evaluates a quantifier body with the fresh hole in
  exactly the parameter's slot, so a dependent type can mention its
  quantified variable without index drift.

## Decidability (termination guards)

The checker is made total by four **termination guards, not typing
rules**. None of them is a typing rule; each turns a non-termination
into an error:

| Guard | Limit | Where |
| --- | --- | --- |
| Per-top-level-unification work budget | 250 steps | `core/unify` (`unify_budget_limit`) |
| Deferred-queue cap | 512 constraints | `core/unify` (`deferred_queue_limit`) |
| Occurs-check depth | 200 | `core/occurs` (`occurs_depth_limit`) |
| eval↔quote cycle depth | 10 000 (panics) | `core/eval`, `core/quote` (`max_depth`) |

The 250 budget is deliberately *just above* the largest legitimate
unification (measured ~76 steps for the prelude plus a two-test
module) and low enough that a cyclic descent errors before its
re-expanded module records make each step's structural hashing
expensive. A large legitimate module *can* exceed it and fail with
`UnificationNotTerminating`; treat the number as a tunable with a
measurement note. The principled endgame is a structural termination
argument for the unification fragment in use (the `For`-instantiation
+ occurs-check combination), which would let the budget be deleted.

## Admitted unsoundnesses (pinned, not fixed)

These are deliberate approximations, each pinned by a test so that a
future fix is a conscious decision rather than a silent change in
strictness.

### 1. Non-exhaustive matches silently produce `Err`

`do_match` returns `v.Err` on `MatchReject` — a *concrete* scrutinee
with no matching case — and `infer_match` quotes that as `tm.Err` with
type `v.Err`, **recording no error**. So

```tao
let x = match 1 { | 0 => True }   // type-checks; x evaluates to Err
```

passes the checker. The pattern *type-checks* against the scrutinee
type (`0` and `1` are both `Int`) but the *value* does not match —
exactly the case a totality checker should reject (Idris/Agda make this
a compile error).

Why it is not fixed yet: the fix is small and principled —
`infer_match` already has the three-valued result; report a
`MatchNoCase`-style error on `MatchReject` (guarded by
`arg_val ≠ v.Err` to avoid cascading errors after a real type error).
Desugared `let`-patterns and function-argument unpacking matches are
safe: their scrutinees are neutral, so they are `MatchNeutral`, never
`MatchReject`. What it needs is a decision, because making it an error
changes which programs compile.

### 2. Exists semantics for neutral matches (`discharge`)

A neutral match has the expected type if *some* case body has it — so
a match with one `Bool` and one `Int` body type-checks against `Int`,
and the incompatible case is silently dropped:

```tao
fn f(x: Int) -> Int = match x { | 0 => True | _ => 2 }   // passes
```

Pinned by `known_unsound_mixed_case_bodies_test`
(`test/tao/deferred_constraint_test.gleam`). Closing this needs
**reachability analysis** — a case is checkable only if its pattern can
match the neutral scrutinee's type — not a change to the quantifier.
That is a real feature, not a patch.

### 3. Unchecked overload return types (`discharge`)

A nested overload dispatch (`NCall`) has its declared return type
unified with the expected value *only at the top level* of a
constraint; nested under an `NApp`, it re-defers without ever checking:

```tao
fn g(x: Float) -> Int = x + 1.0   // passes; body evaluates to Float
```

Pinned by `known_unsound_overload_return_test`. Both corner cases
require a neutral match type, as produced by overloaded dispatch;
ordinary implicit-arg functions are not affected.

### 4. `check_lit` subtyping with no range check

An int literal type-checks against *any* int literal type and is
silently converted to a float for float types — no range check for
fixed-width ints:

```tao
let x: I8 = 300   // passes
```

Documented in `core/infer`'s `check` docs. Minor.

### 5. `is_type_ctor` global environment scan

`Ctr(tag) ~ Typ(0)` is accepted if *any* type definition in scope has
a variant with that tag (`core/unify`, `is_type_ctor`). The rule
depends on ambient scope, not just the two values: a value like
`#None{}` (an `Option` variant) is accepted as a *type* value in any
type position. It exists because a GADT value's type is its variant's
constructor application, and that must be usable as a type value.
Minor, but it is the one unification rule that looks at the
environment.

### 6. `Fix` unification is a heuristic, not a rule

Two `Fix` values unify by unfolding one step each and unifying the
results (`core/unify`, `Fix` case). Coinductive equality of recursive
values is undecidable in general; one-step unfolding is a sufficient-ish
condition that can reject valid equalities and — combined with the
permissive `discharge` — can accept non-equivalent recursive values.
Acceptable for this restricted domain, but it is not a standard
unification rule and should be treated as an approximation.

### 7. `eval`'s out-of-range `Var` → `v.Err`

A `Var` index beyond the environment evaluates to `v.Err` silently
(`core/eval`). This is inside the documented undefined-behavior zone:
it is only reachable under type errors, where evaluation is not
guaranteed.

## Ad-hoc edges (correct today, worth knowing)

* **`infer_app` routes only `NHole`/`NMatch` neutral heads to
  `infer_app_neut`** (`core/infer`, marked `TODO`): an `NApp`/`NCall`/
  `NVar` function head gets `NotAFunction` instead of being deferred.
  The principled rule is that *any* neutral head may become a `Pi`
  once it resolves, so all neutrals should route through
  `infer_app_neut`; only a *concrete* non-`Pi` is definitely not a
  function. The change is safe (it only adds acceptances where there is
  currently an error).
* **`discharge_match_case` backtracks by counting total errors** —
  "did `ctx.errors` grow" is the proxy for "unification failed". Works
  because `with_err` dedupes; if two cases produce the *same*
  deduplicated error, the second is treated as successful and its
  substitutions are committed (harmless — the program errors either
  way). A `Result(Context, Error)` unification API would be cleaner.
* **`resolve.term` quotes hole solutions against the *solve-time*
  env, not the term's frame**: a resolved term is only valid in the
  solve-time frame. Holds in practice because body terms are only
  written/quoted while their binders are in scope, but it is an
  unenforced invariant.
* **`define.types` checks `FnDef` bodies eagerly in phase 1**, while
  the module doc claims "every module record exists before any body is
  checked". The claim holds only because imports are prepended to the
  def list and `type_name` lazily runs phase 1 for imported modules —
  a subtle order-dependence. The `TODO` in `type_stmt_data` points at
  the simplification: defer `FnDef`/`FnOverload` bodies to phase 2 like
  `LetVar`, making the two-phase invariant literally true.

## Where the gaps are pinned

| Gap | Test |
| --- | --- |
| Exists semantics | `known_unsound_mixed_case_bodies_test` (`test/tao/deferred_constraint_test.gleam`) |
| Unchecked overload returns | `known_unsound_overload_return_test` (same file) |
| Imported type defs in fn bodies | `fn_body_uses_imported_type_def_test`, `fn_body_uses_imported_ctor_annot_test` (`test/tao/define_test.gleam`) |
| Implicit-arg invariants | `test/tao/implicit_args_test.gleam` |
