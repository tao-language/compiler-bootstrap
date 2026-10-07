# Implicit Arguments

Tao functions can be *polymorphic*: a parameter in angle brackets is an
**implicit argument** — a quantified type argument the caller never writes.
The type checker infers it at every call site:

```tao
fn identity<a>(x: a) -> a = x

>>> identity(42)    42
>>> identity(True)  True
```

There can be zero or more implicit arguments:

```tao
fn pair<a, b>(x: a, y: b) -> a = x

>>> pair(1, True)   1
>>> pair(True, 1)   True
```

In Tao, types are first-class values, so polymorphism is not a meta-level
annotation: `fn f<a>(x: a)` is the *value* `for a. ...`, and calling `f`
is ordinary application of that quantifier (next section). The prelude's
`option._or` is an implicit-arg function:

```tao
// lib/prelude/v0.0.1/option.tao
fn _or<a>(option: Option(a), default: a) -> a
= match option {
| Some(x) => x
| None => default
}
```

## Syntax

```tao
fn name<imp1, imp2: Type>(x: imp1, ...) -> ret
= expr                     // expression body
fn name<...>(...) { stmts }  // block body (statements only)
```

* The angle-bracket list is parsed by the **same `parameters` combinator**
  as the argument list (`tao/parse`, `fn_def_body`), so an implicit can
  carry a type annotation (`a: Type`) and even a default — but desugaring
  only accepts a **plain type variable** for each implicit (an
  unannotated implicit gets a fresh hole); anything else hits the
  `error: implicit parameter must be a plain type variable` guard in
  `tao/desugar`.
* Callers write `name(args)` — there is no type-argument syntax.
* **Explicit type application is planned**: `identity<Int>(42)` would
  behave like a check annotation ("check this"), not a hole: the written
  type would be unified against the instantiated one instead of leaving a
  hole for inference. Today only the implicit form `identity(42)` is
  supported. The `AppExpectedExplicitArg` error ("expected explicit
  argument, got implicit argument") is the reserved message for that
  syntax and is not constructed anywhere yet.
* Not every Tao AST form is parseable yet (e.g. the `FnT` function-type
  expression has no parser rule); the direction is that the whole AST
  becomes parseable.

## How it works

### 1. Desugaring (`tao/desugar`)

`fn_def` desugars to one nested **`for` binder per implicit** (outermost
first) + a lambda over the single `__args` record + a match that unpacks
the record into the parameter patterns (`function`/`function_inner`),
wrapped in `fix name` when the body is self-recursive:

```tao
fn is_empty<a>(xs: List(a)) -> Bool =
  match xs {
  | Nil => True
  | Cons(_, _) => False
  }
```

```core
%for(a).                                       // the implicit argument
  %lam(__args: {`1`: #List({``: a})}) =>       // argument record, typed in the `for` frame
    %(%letp {`1`: xs} = __args;                // unpacking match (single case)
      %match (xs) {
      | #Nil({}) => #True
      | #Cons({``: _, ``: _}) => #False
      }: #Bool)
```

(Backticked `` `1` `` and `` `` `` are the positional (numbered /
empty-named) record fields. The implicit's parameter type is absent in
Core — `infer_for` gives it a fresh hole, next section.)

Two deliberate choices, both about de Bruijn frames:

* **With implicits, the `__args` record type is built in the `for`
  frame.** The annotations mention the implicits, which are bound there,
  so they carry the implicits' own indices. Leaving the record type a
  hole instead would defer solving the annotations to the unpacking
  match, where the implicits sit *below* the record and pattern
  bindings; re-evaluating such a record in the `for` frame then binds
  those names to unrelated environment slots (module records) — the
  corruption behind the original non-termination bug.
* **Consequently, per-parameter annotation checks are skipped in the
  unpacking match when implicits are present** (`parameters_unpack`'s
  `skip_checks`): the lambda's domain is already the fully-typed record,
  so the call-site unification checks everything. *Without* implicits
  the record stays a hole and each annotation is checked inside the match
  as `let __checkN: type = param` — there, an annotation may mention a
  **sibling explicit parameter** (`fn eval(a: Type, e: Expr(a))`), which
  is not in scope at the lambda's parameter-type position.

`FnT` (a function *type*, `function_type`) desugars similarly: a single
`for __impl` binding the whole implicits record, unpacked into the
monomorphic `pi` body. Overloaded functions use the same mechanism with
`__type` as the quantified variable (see [overloads.md](overloads.md)).

### 2. Generalization (`core/infer`, `infer_for`)

`infer_for` infers the implicit's type (a fresh hole when unannotated),
evaluates it to a value, pushes the variable onto the context, infers the
body, **quotes the body's type while the parameter is still in scope**
(the type may depend on it — `a -> a`), and pops. The result is the
value

```
For(captured_env, (name, param_type), body_type_term)
```

where `body_type_term` is a *term* whose de Bruijn indices address
`[param, ..captured_env]`. This is let-polymorphism: the function's type
is `∀a. {1: a} → a`, stored as data.

### 3. Instantiation at the call site (`core/infer`, `instantiate`)

This is the heart of implicit arguments. When `infer_app` applies a
function, it first runs `instantiate` on the function's type: **each `For`
quantifier is instantiated with a fresh hole** — the hole is prepended to
the quantifier's captured environment (taking exactly the parameter's
slot, so the quoted body term's indices line up by construction), the body
type is re-evaluated in that environment, the function is re-applied to
the hole *term*, and the process recurses until a `Pi`:

```
is_empty(Cons(1, Nil))
  → is_empty(?h)({1: Cons(1, Nil)})          -- ?h is the implicit argument
```

The `Pi` domain `{1: #List({1: ?h})}` is then checked against the
argument's type `{1: #Cons({1: %Int, 2: #Nil})}` — a value's type is its
constructor application, so the `Cons` *variant's* — and GADT
unification (`unify_gadt`) solves `?h := %Int`. The codomain is evaluated
with the argument value prepended, so dependent return types work.

The same fresh-hole rule is used by `unify` itself whenever a `For` meets
a non-`For` value (and `For`~`For` instantiates both sides), so
*application and unification agree on what a quantifier means*.

Every hole is solved by `solve_hole` with an **occurs check**
(`core/occurs`): a hole meeting a solution that contains itself is an
`InfiniteType` error, so the instantiation rule cannot manufacture
non-well-founded types. Constraints that cannot be decided while a side
is neutral go to the deferred queue and are retried on every solve.

### 4. Evaluation (`core/eval`) — the evaluator stays blind

A `For` value β-reduces exactly like a `Lam` (`do_app`): the body is
evaluated in `[arg_val, ..captured_env]`. The implicit argument is a
term-level hole, whose value is a neutral `NHole`, so a body that depends
on it (the overload dispatch match on `__type`, a record type mentioning
`?h`) gets stuck as an `NMatch`/neutral and re-reduces through `unwrap`
once the hole is solved.

The invariant is the same as for overloads: **eval does no type
lookups** — no type definitions, no environment introspection, no error
reporting. A value depends only on its term. *If* infer/check report no
errors, evaluation is correct; with errors it is undefined behavior.

### 5. Resolution (`core/resolve`)

`resolve.context` (run at the end of `compile.modules`) discharges the
leftover deferred constraints, then resolves every hole in the
environment, the type bindings, and the accumulated errors. `resolve.term`
rewrites term-level holes with their quoted solutions — quoted against
the *solve-time* captured environment, with a `seen` stack breaking
self-referential cycles. After resolution, test terms are concrete and
evaluate directly: `pair(1, True)` reduces to `#Pass`.

You can inspect the inferred type of a definition with

```sh
gleam run -- debug-src 'fn pair<a, b>(x: a, y: b) -> a = x' \
  --add=prelude --dump-def=pair
```

```
// type of pair (names n0..n15 are de Bruijn indices)
FOR a (envlen=9)
  body:
%for(b: ?100).
  %pi(__args: {`1`: n14, `2`: b}) -> n14
```

i.e. `∀a. ∀b. {1: a, 2: b} → a` — the indices are rendered against a flat
names list (`n15` is the innermost binder, so `n14` here is the `a` bound
by the outer `for`).

## Soundness

The mechanism is principled because it introduces **no non-standard
typing rule**:

* `fn f<a>(x: a)` is ordinary let-generalization: the defined name is
  bound to `∀a. {1: a} → ...`.
* The call site applies the standard **instantiation rule** of
  polymorphic function application (System F / Hindley–Milner): one
  *fresh* type variable per quantifier, substituted under the body.
  Freshness is what makes the rule sound — the new variable cannot
  alias any existing type, so no information is assumed.
* The fresh variables are holes; they are solved only by unification with
  the `Pi` domain (or later constraints), and `solve_hole` runs the
  **occurs check** before committing a solution, so the rule cannot
  produce infinite types.
* **De Bruijn discipline** keeps the re-evaluation honest: values address
  environment entries by *level* (stable under push/pop), terms by
  *index* (converted with `index = env_size - level - 1`, guarded by an
  `assert` in `quote`). `instantiate` re-evaluates the quoted body type
  with the hole in exactly the parameter's slot, and `infer_for` quotes
  the body type while the parameter is still pushed — so a dependent type
  can mention its quantified variable without index drift.
* **Termination guards** make the checker total on this input class
  (none of them are typing rules): a per-top-level-unification work
  budget (250 steps) and a deferred-queue cap (512) turn cyclic
  re-expansion into `UnificationNotTerminating`; the occurs check is
  depth-bounded (200); the eval↔quote cycle is depth-bounded (10 000) and
  panics with a message pointing here.
* **Regression coverage** pins the former failure modes
  (`test/tao/implicit_args_test.gleam`): two tests of one implicit-arg
  function, multiple implicits, and the prelude's overloaded `_or` —
  together with invariant probes that no hole is ever solved with a rigid
  `NVar` or with a module record in the test phase, and that module
  records carry no positional `""` fields.

## Known unsoundnesses (pinned, not fixed)

`resolve.discharge` admits two deliberate approximations, pinned by the
`known_unsound_*` tests in `test/tao/deferred_constraint_test.gleam`:

* **Exists semantics for neutral matches.** A neutral match has the
  expected type if *some* case body has it — so a match with one `Bool`
  and one `Int` body type-checks against `Int`. The incompatible case is
  silently dropped.
* **Neutral case bodies re-defer** without ever checking an `NCall`'s
  declared return type (an overload dispatch nested under another).

Both are corner cases of *deferred* constraints (they require a neutral
match type, as produced by overloaded dispatch); ordinary implicit-arg
functions are not affected.

## Limitations

* **Recursive implicit function types** are not supported: a
  self-referential type makes the eval↔quote cycle spin until the depth
  bound panics with "recursive implicit function types are not supported
  yet; see docs/implicit-args.md".
* **With implicits, a parameter annotation may not mention a sibling
  *explicit* parameter** (`fn f<a>(x: a, y: List(x))` → `undefined
  variable "x"`): the record type is built in the `for` frame, where
  explicit parameters are not bound. Without implicits, sibling
  references work (checked inside the unpacking match).
* **Return-type annotations cannot mention any parameter** — the
  annotation is wrapped around the unpacking match, outside the
  parameter bindings.
* **Implicits must be plain type variables** (desugaring guard).
* **No explicit type application yet** (`identity<Int>(42)` is not
  parsed); see the note in Syntax.
* **A wrong argument type to an implicit-arg function does not always
  produce a build error** — e.g. `is_empty(1.5)` compiles clean and the
  test simply fails at evaluation. Pinned by
  `wrong_arg_type_test_fails_test`; a real type error would be an
  improvement, but is not required.
* **Parser coverage is partial** (e.g. `FnT`); the direction is a
  fully-parseable AST.

## Where to look

| Phase | File | Key functions |
| --- | --- | --- |
| Syntax | `src/tao/parse.gleam` | `fn_def_body` |
| Surface AST | `src/tao/ast.gleam` | `FnDef`, `Fn`, `FnT`, `Parameters` |
| Desugaring | `src/tao/desugar.gleam` | `function`, `function_inner`, `parameters_unpack`, `function_type` |
| Generalization | `src/core/infer.gleam` | `infer_for` |
| Instantiation | `src/core/infer.gleam` | `instantiate`, `infer_app` |
| Unification | `src/core/unify.gleam` | `For` cases, `solve_hole`, `defer`/`retry_deferred` |
| Occurs check | `src/core/occurs.gleam` | `occurs` |
| Evaluation | `src/core/eval.gleam` | `do_app` (`For` case), `do_match` |
| Quoting | `src/core/quote.gleam` | `quote`, `quote_case` |
| Resolution | `src/core/resolve.gleam` | `context`, `term`, `discharge` |
| Prelude example | `lib/prelude/v0.0.1/option.tao` | `_or<a>` |
| Tests | `test/tao/implicit_args_test.gleam`, `test/tao/deferred_constraint_test.gleam` | |
