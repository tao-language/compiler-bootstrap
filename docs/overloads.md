# Function Overloads

Tao has a syntax for *overloaded functions*: one name dispatches to
different definitions depending on the **types of the arguments**. The
prelude's operators are defined this way:

```tao
// lib/prelude/v0.0.1/operators/and.tao
import prelude/bool {Bool}

fn (and) {
| bool._and(Bool, Bool)
}
```

```tao
>>> True and False  False
```

The parentheses around the name are required when the name is a reserved
word or an operator (`and`, `or`, `+`, ...); ordinary names are written
without them (`fn mix { | ... }`).

## Syntax

```tao
fn (name) {
| [module.]function(Type1, Type2, ...) [if guard]
| ...
}
```

* A **choice** names the definition to use. The optional module qualifier
  refers to a definition of another module (`bool._and` is the `_and`
  field of the `prelude/bool` module record); unqualified names refer to
  definitions of the current module.
* The choice's arguments are **patterns** matched against the
  *arguments' types* — in practice type names (`Bool`, `Option(Int)`),
  but literal types (`Int`), type variables and wildcards also work.
* Choices are tried **in order**; the first whose pattern matches the
  arguments' types wins. If none matches, the dispatch match falls
  through and the expression evaluates to an error (tests print
  `%error`).

## How it works

### 1. Desugaring

`fn (name) { | c1 | c2 }` desugars to a polymorphic function that
matches the **type of its argument record** against the choices'
patterns (`tao/desugar`, the `FnOverload` case):

```core
let name =
  for __type: %Type {
    lam __args: __type {
      match __type {
      | <pattern of c1> => <c1's function>(__args)
      | <pattern of c2> => <c2's function>(__args)
      }
    }
  }
```

The argument record is the single record the call syntax produces
(`a op b` desugars to `op({1: a, 2: b})`). `__type` is the *type* of
that record: for `True and False` it is `{1: #True{}, 2: #False{}}`.

### 2. Choice expansion (compile time)

A value's type is its **constructor application**, and for ADT/GADT
values that is the *variant's* constructor application: the value
`True` has type `#True{}`, not `#Bool{}`. (When only a declared type is
known — e.g. a variable `a: Bool` — the type is the type constructor
application `#Bool{}`.) Both are legitimate values of `%Type`, so a
choice pattern `Bool` must match **both** the type constructor form and
every variant's constructor form.

Core patterns have no disjunction, and the evaluator must stay blind
(it does no type lookups — see the design note below), so the type names
are expanded at compile time: `tao/define`'s
`expand_overload_choices` (run from `stmt_value` before desugaring)
rewrites each type-name pattern into

* the pattern **as written** (the type constructor application, e.g.
  `Bool` → matches `#Bool{}`), plus
* one pattern **per variant** of the type, constructor tag with an open
  (any) argument record (e.g. `True` → matches `#True{..}`).

Since one pattern can name several alternatives, each choice is
replicated for the **product** of its arguments' alternatives.
`| bool._and(Bool, Bool)` becomes nine cases:

```core
match __type {
| {1: Bool,   2: Bool}   => bool._and(__args)
| {1: Bool,   2: True}   => bool._and(__args)
| {1: Bool,   2: False}  => bool._and(__args)
| {1: True,   2: Bool}   => bool._and(__args)
| {1: True,   2: True}   => bool._and(__args)
| {1: True,   2: False}  => bool._and(__args)
| {1: False,  2: Bool}   => bool._and(__args)
| {1: False,  2: True}   => bool._and(__args)
| {1: False,  2: False}  => bool._and(__args)
}
```

(`gleam run -- debug-expr "True and False"` prints this match after
inference.) Names that do not name a type definition are left unchanged:
the type checker reports them as errors (next section).

### 3. Type checking

The dispatch match is checked like any other match: each choice pattern
is checked against the scrutinee's type `%Type` (`__type` is the
`for`'s parameter). A constructor application is a value of `%Type`
only when its tag names a type definition **or a variant of one** —
`core/unify`'s `Ctr`-vs-`Typ(0)` rule (`is_type_ctor`). This is why
choice patterns may only name types, and why typos in choice types are
reported:

```tao
fn (and) {
| bool._and(Nope, Nope)  // ❌ type mismatch: #Nope is not a type
}
```

The choice's *body* is then type-checked as usual; applying
`bool._and(__args)` unifies the chosen function's parameter type
(`{1: #Bool{}, 2: #Bool{}}`) with the actual argument types
(`{1: #True{}, 2: #False{}}`) through the ordinary GADT unification
(`unify_gadt`).

### 4. Calling

`True and False` desugars to `and({1: True, 2: False})`. During
inference the `for` quantifier is instantiated with a fresh hole and the
term becomes `and(?h)({1: True, 2: False})`, where checking the
argument record against the lambda's domain solves
`?h := {1: #True{}, 2: #False{}}` — the **type record** of the
arguments. Both the expression's *type* (the dependent match type,
evaluated with `?h`) and its *value* (the `for`/`lam` β-reduce, then
the dispatch match runs with `?h`) run the **same blind match**: tag
equality on the constructor applications. Since the choice patterns were
expanded to concrete tags (`Bool`/`True`/`False`), the right case is
selected without the evaluator knowing anything about type definitions.
The case body then applies the chosen function to the **value** record
`{1: True, 2: False}`.

### 5. Shadowing

The prelude is implicitly imported into every module, and the prelude
itself defines operators (`and`, `+`, ...). A module that defines `and`
locally must have its definition **shadow** the imported one:
`tao/define` skips import entries whose name is defined locally
(`shadowed_imports`), so the local definition — not the prelude's — is
registered in the module record. (Without this, the import, processed
first, would occupy the record's entry and the local definition's body
would never be type-checked.)

## Design note: the evaluator stays blind

The type-definition knowledge lives in the **compiler** phases, never in
the evaluator:

* `define.expand_overload_choices` rewrites choice patterns at compile
  time, using `context.lookup_type_def`;
* `unify`'s `Ctr`-vs-`Typ(0)` rule validates choice patterns at check
  time;
* `eval.match_pattern` blindly matches tags, records and literals with
  no environment and no lookups.

The invariant: *if infer/check reports no errors, evaluation is
correct*; with errors, evaluation is undefined behavior. Keeping eval
blind means a term's value depends only on the term, not on the module
records that happened to be in scope.

## Limitations

* **Top-level overloads only.** Choice expansion happens in
  `define.stmt_value`, which processes top-level definitions. An
  overload written inside a function body (`fn f() { fn (g) { ... } }`)
  desugars without expansion, so its dispatch only matches the type
  constructor form (`#Bool{}`), not the variant forms — calls with
  concretely-typed arguments (`True`) would not dispatch.
* **Variant patterns are tag-only.** The per-variant alternatives match
  the constructor tag with *any* argument record, so a choice named
  `Option(Int)` also matches arguments whose type is `#Some{a: Float}`.
  The over-approximation degrades gracefully: the chosen function's own
  argument match fails and the expression evaluates to an error.
* **Order matters.** Choices (and therefore their expanded cases) are
  tried in written order; put the most specific choices first.
* **Case blow-up.** A choice with *n* type-name arguments expands to the
  product of (1 + variants) per argument. Fine for the prelude's
  small types; for large types prefer plain functions with a single
  choice or explicit matches.
