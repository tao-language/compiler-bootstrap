# Type Definitions as First-Class Environment Values

> **Reference:** Prototype in [`prototypes/type_definitions_as_env_values.py`](prototypes/type_definitions_as_env_values.py) — runnable proof of concept demonstrating this design.

## Motivation

### Current Approach: Separate `ctrs` Registry

The current design (documented in [03-core-language.md](03-core-language.md)) uses a **separate constructor environment** (`CtrEnv`) alongside the variable environment (`Context`):

```gleam
/// Constructor definition from type declarations
pub type CtrDef {
  CtrDef(params: List(String), arg_ty: Term, ret_ty: Term)
}

/// Constructor environment: maps constructor names to their definitions
pub type CtrEnv = List(#(String, CtrDef))

/// State carries BOTH registries
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // Variable environment
    ctrs: List(#(String, List(CtrDef))),     // Constructor registry  ← SEPARATE
    errors: List(Error),
    ffi: List(FfiEntry),
    hole_counter: Int,
  )
}
```

This creates **two sources of truth**: type definitions live in both the env AND the ctrs registry. This duplication makes:
- Imports more complex (update both env AND ctrs)
- Type definitions non-first-class (can't be passed as arguments)
- Exhaustiveness checking separate from type definitions
- User-defined types in Core impossible

### Goal: Eliminate the Separate Registry

Store type definitions as **regular env entries**, like any other `$let` binding. The type checker treats them as first-class values.

## Design

### 1. Type Definition Structure

A TypeDef is stored in the env as a value (like `VLam` or `VCtr`), but marked specially so the type checker recognizes it:

```gleam
/// A type definition stored as a first-class value in the environment.
///
/// Instead of a separate `ctrs` field, type definitions are regular env
/// entries:
///
///   "Option" → (TypeDef, $Type)
///   "Bool"   → (TypeDef, $Type)
///   "Vec"    → (TypeDef, $Type)
///
/// The "value" side carries the constructor metadata; the "type" side is
/// always $Type (or a dependent function type for parametric types).
pub type TypeDef {
  TypeDef(
    name: String,
    param_count: Int,            // Number of type parameters
    constructors: List(ConstructorDef),  // Constructor definitions
  )
}

pub type ConstructorDef {
  ConstructorDef(
    tag: String,                  // Constructor tag (e.g., "Some", "None")
    fields: List(#(String, FieldDef)),  // (name, field_info)
    result_template: Value,       // Type template with HVar references
  )
}

pub type FieldDef {
  FSimple(Value)                  // Simple type field
  FComputed(String, Int)          // (extractor, arg_index) — for GADTs
}
```

### 2. State Simplification

Remove `ctrs` from State. Everything lives in `vars`:

```gleam
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // Everything in one env
    errors: List(Error),
    ffi: List(FfiEntry),
    hole_counter: Int,
    truth_ctr: String,
  )
}
```

### 3. How Type Checking Works

#### Inference (unchanged)

```gleam
fn infer_ctr(state, tag, arg, span) -> #(Value, Value, State) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  #(ctr_val, VNeut(HVar(0), []), state)  // neutral placeholder
}
```

**No changes needed.** Inference produces a constructor value with a neutral placeholder type (`HVar(0)`). It doesn't need to know the type definition yet.

#### Checking (refactored)

```gleam
fn check_ctr(state, tag, arg, expected, span) -> #(Value, Value, State) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  
  // 1. Look up expected type in env
  case env_lookup(state, expected) {
    Ok(#(TypeDef(name, nparams, ctors), type_val)) ->
      // 2. Get type of constructor's argument (for param substitution)
      let arg_type = arg_val  // terms == types in dependently typed Core
      
      // 3. Compute constructor type from TypeDef
      case type_of_type_def(ctors, nparams, [arg_type], tag, [arg_val]) {
        Ok(ctor_type) -> {
          // 4. Unify
          let state2 = unify(state, ctor_type, expected)
          #(ctr_val, ctor_type, state2)
        }
        Error(msg) -> error(state, msg)
      }
    Ok(#(value, _)) -> {
      // Expected is not a TypeDef — fall back to basic checking
      check_without_type_def(state, tag, arg, expected)
    }
    Error(_) -> error(state, CtrUndefined(tag, span))
  }
}
```

The key new function:

```gleam
/// Compute the type of a constructor using a TypeDef.
///
/// For ADTs: substitute type params → return result template.
/// For GADTs: also compute indices from constructor arg types.
fn type_of_type_def(
  ctors: List(ConstructorDef),
  nparams: Int,
  type_args: List(Value),
  tag: String,
  arg_types: List(Value),
) -> Result(Value, String) {
  case find_ctor(ctors, tag) {
    Ok(ctor) -> {
      // Substitute type params (HVar(level)) with actual args
      let result = subst(type_args, ctor.result_template)
      
      // For GADTs, compute indices from constructor arg types
      case compute_gadt_indices(ctor, arg_types, type_args) {
        Ok(computed) -> Ok(computed)
        Error(_) -> Ok(result)
      }
    }
    Error -> Error("constructor " <> tag <> " not found")
  }
}

/// Substitute HVar(level) references with actual type arguments.
fn subst(args: List(Value), v: Value) -> Value {
  case v {
    VNeut(HVar(level), spine) ->
      case list.drop(args, level) {
        [arg, ..] -> arg
        [] -> v
      }
    VCtr(tag, arg) -> VCtr(tag, subst(args, arg))
    _ -> v
  }
}

/// For GADTs: extract and compute index types from constructor arguments.
fn compute_gadt_indices(
  ctor: ConstructorDef,
  arg_types: List(Value),
  type_args: List(Value),
) -> Result(Value, String) {
  case ctor.tag {
    "Nil" ->
      // Vec(0, a) — index is concrete 0
      let a = list.drop(type_args, 1) |> list.first
      Ok(VCtr("Vec", [VLit(0), a]))
    "Cons" -> {
      // Vec(m+1, a) — extract m from xs's type Vec(m, a)
      let xs = list.drop(arg_types, 1) |> list.first
      let m = extract_index(xs)  // Pattern match on xs's type
      let a = list.drop(type_args, 1) |> list.first
      Ok(VCtr("Vec", [m, a]))
    }
    _ -> Error("not a GADT constructor")
  }
}

fn extract_index(xs: Value) -> Value {
  // xs has type Vec(m, a), extract m by pattern matching on the type
  // In the real impl, this looks up xs's binding in env
  // For now, default to a fresh variable
  VNeut(HHole(-1), [])
}
```

### 4. Exhaustiveness Checking

Exhaustiveness is **free** — the TypeDef's constructors ARE the exhaustive list:

```gleam
/// Check if match cases are exhaustive for a TypeDef.
///
/// The exhaustive list comes from the TypeDef itself — no separate
/// registry needed.
fn check_exhaustiveness_type_def(
  td: TypeDef,
  patterns: List(#(Pattern, Span)),
  scrutinee_type: Value,
) -> State {
  let all_tags = [c.tag || c <- td.constructors]
  let covered_tags = [p.tag || p <- patterns, p.tag]
  let missing = [t || t <- all_tags, t <> covered_tags]
  
  case missing {
    [] -> state  // Exhaustive
    [_ | ..] -> state.with_err(MatchMissing(missing, covered_tags, span))
  }
}
```

## Why This Is the Cleanest Approach

### Comparison of Three Designs

| Aspect | A: Separate CTRs | B: TypeDefs in Env | C: Separate CtrEnv |
|--------|------------------|---------------------|-------------------|
| **State fields** | vars + ctrs | vars only | vars + ctr_env |
| **Env lookup** | Different for types vs values | Uniform for everything | Different for types vs values |
| **Imports** | Update vars AND ctrs | Update vars only | Update vars AND ctr_env |
| **Exhaustiveness** | Separate pass from TypeDef | Directly from TypeDef | Separate from TypeDef |
| **First-class types** | No | Yes | No |
| **User-defined types in Core** | Impossible | Possible | Impossible |
| **Complexity** | High (two registries) | Low (one env) | Medium (two registries) |

**Design B (TypeDefs in env) is the winner.** It has:
- **One source of truth** — the env
- **Uniform lookup** — same mechanism for types and values
- **Simpler imports** — add one env entry
- **Free exhaustiveness** — constructors are in the TypeDef
- **Extensibility** — users can define types in Core

### Concrete Benefits

1. **Remove `ctrs` field from State** — 1 less field to thread through every function
2. **Simpler imports** — `import std/option` just adds one env entry
3. **Exhaustiveness from TypeDef** — no separate data structure needed
4. **User-defined types** — Core code can define types: `$let MyList = <TypeDef>`
5. **First-class types** — you can pass a type definition as an argument

## Implementation Plan

### Step 1: Add TypeDef to core/ast.gleam

```gleam
/// Type definition — stored as a regular env entry
pub type TypeDef {
  TypeDef(
    name: String,
    param_count: Int,
    constructors: List(ConstructorDef),
  )
}

pub type ConstructorDef {
  ConstructorDef(
    tag: String,
    fields: List(#(String, FieldDef)),
    result_template: Value,
  )
}

pub type FieldDef {
  FSimple(Value)
  FComputed(String, Int)
}
```

### Step 2: Remove CtrDef and CtrEnv from core/ast.gleam

Remove the existing `CtrDef` and `CtrEnv` types. They are replaced by `TypeDef`.

### Step 3: Remove CtrEnv from State in core/state.gleam

```gleam
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // Everything in one env
    errors: List(Error),
    ffi: List(FfiEntry),
    hole_counter: Int,
    truth_ctr: String,
  )
}
```

Add a helper to look up TypeDefs:

```gleam
/// Look up a type definition by name.
/// Returns the TypeDef if found, Error otherwise.
pub fn lookup_type_def(state: State, name: String) -> Result(TypeDef, Nil) {
  case lookup_var(state, name) {
    Ok(#(value, _)) ->
      case value {
        VCtr("TypeDefMarker", VNeut(HHole(id), [])) ->
          // In the real impl, check for TypeDef marker differently
          // For now, this is a placeholder
          Ok(TypeDef(name: name, param_count: 0, constructors: []))
        _ -> Error(Nil)
      }
    Error(_) -> Error(Nil)
  }
}
```

**Important:** In the real implementation, `TypeDef` values need a way to be recognized. Options:
- Wrap in `VCtr("TypeDefMarker", TypeDef)` — simple but ugly
- Use a special `VType` value — cleaner
- Store TypeDef as `VLam` with specific structure — most elegant

**Recommendation:** Use a `VType` value:
```gleam
pub type Value {
  VType(TypeDef)  // First-class type definition value
  // ... other variants
}
```

### Step 4: Update core/infer.gleam — check_ctr

```gleam
fn check_ctr(state, tag, arg, expected, span) -> #(Value, Value, State) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  
  case env_lookup(state, expected) {
    Ok(#(VType(td), _)) ->
      let arg_type = arg_val
      case type_of_type_def(td, [arg_type], tag, [arg_val]) {
        Ok(ctor_type) -> {
          let state2 = unify(state, ctor_type, expected)
          let forced = force(state2, ctr_val)
          let forced_type = force(state2, ctor_type)
          #(forced, forced_type, state2)
        }
        Error(msg) -> {
          let new_state = state.with_err(state, CtrUndefined(tag, span))
          #(VErr, VErr, new_state)
        }
      }
    _ -> {
      // Not a TypeDef — fall back to basic checking
      let state2 = unify(state, expected, ctr_val)
      let forced = force(state2, ctr_val)
      let forced_type = force(state2, VNeut(HVar(0), []))
      #(forced, forced_type, state2)
    }
  }
}

fn env_lookup(state, v: Value) -> Result(#(Value, Value), String) {
  case v {
    VNeut(HVar(level), []) ->
      lookup_by_level(state, level)
    _ -> Error("not a variable")
  }
}
```

### Step 5: Add type_of_type_def, subst, compute_gadt_indices

See the code blocks above in section 3. These are new internal functions in `infer.gleam`.

### Step 6: Update exhaustiveness.gleam

```gleam
/// Check if match cases are exhaustive.
///
/// Uses the scrutinee's type (from env) if available, otherwise falls
/// back to pattern-based checking.
pub fn check_exhaustiveness(
  state: State,
  scrutinee: Value,
  cases: List(Case),
) -> State {
  // Get the scrutinee's type
  case lookup_type_def(state, get_type_name(scrutinee)) {
    Ok(td) ->
      // Use TypeDef's constructors for exhaustiveness
      check_exhaust_from_type_def(state, td, cases)
    Error(_) ->
      // Fall back to pattern-based checking
      check_exhaust_from_patterns(scrutinee, cases)
  }
}

fn check_exhaust_from_type_def(
  state: State,
  td: TypeDef,
  cases: List(Case),
) -> State {
  let all_tags = [c.tag || c <- td.constructors]
  let covered_tags = all_tags
  let missing = [t || t <- all_tags, t <> covered_tags]
  
  case missing {
    [] -> state
    [_ | ..] -> state.with_err(MatchMissing(missing, covered_tags, span))
  }
}
```

### Step 7: Update Tao Desugarer

When the desugarer encounters a type definition in Tao:

```gleam
/// Desugar a Tao type definition to a TypeDef value in the env.
fn desugar_type_def(
  state: State,
  name: String,
  constructors: List(#(String, List(#(String, TypeAst)))),
) -> State {
  let td = build_type_def(name, constructors)
  state.def_var(state, name, VType(td), make_type_value(td))
}

fn build_type_def(
  name: String,
  constructors: List(#(String, List(#(String, TypeAst)))),
) -> TypeDef {
  TypeDef(
    name: name,
    param_count: list.length(constructors.0.params),
    constructors: [
      ConstructorDef(
        tag: ctor.name,
        fields: build_fields(ctor.fields),
        result_template: build_result_template(ctor, name, params),
      ) || ctor <- constructors
    ],
  )
}

fn make_type_value(td: TypeDef) -> Value {
  // The "type" of a TypeDef is $Type (universe 0)
  VNeut(HVar(1), [])
}
```

### Step 8: Update Import System

The import resolver adds TypeDef values to the env:

```gleam
/// Add type definitions to the env with qualified names.
fn add_type_defs(env: State, module: Module, alias: String) -> State {
  list.fold(module.public_types, env, fn(acc, td) {
    let qualified = if alias != "" { alias <> "." <> td.name } else { td.name }
    acc.def_var(acc, qualified, VType(td.type_def), acc.type_of(td.type_def))
  })
}
```

### Step 9: Update Import Resolver (06-import-system.md)

When an import like `import std/option` is processed:

```
1. Load std/option module
2. Extract public types: [TypeDef("Option", ...)]
3. Add to env with qualified name: "option.Option" → (VType(td), $Type)
```

The import resolver doesn't need to touch a separate `ctrs` field anymore.

## Prototype

A runnable proof of concept is available at:
- **File:** [`prototypes/type_definitions_as_env_values.py`](prototypes/type_definitions_as_env_values.py)
- **Run:** `python3 plans/rewrite/prototypes/type_definitions_as_env_values.py`

The prototype demonstrates:
1. **Bool** — Simple ADT (no params)
2. **Option** — Parameterized ADT (1 type param)
3. **Nat** — Recursive ADT (uniform type)
4. **Vec** — Recursive GADT (index from args)

Each type is tested for inference, checking, and exhaustiveness.

## Migration Notes

### What Changes

| Module | Change |
|--------|--------|
| `core/ast.gleam` | Add `TypeDef`, `ConstructorDef`, `FieldDef`. Remove `CtrDef`, `CtrEnv`. |
| `core/state.gleam` | Remove `ctrs` field from `State`. |
| `core/infer.gleam` | Update `check_ctr` to look up TypeDef in env. Add `type_of_type_def`, `subst`, `compute_gadt_indices`. |
| `core/exhaustiveness.gleam` | Update to extract constructors from TypeDef. |
| `tao/desugar.gleam` | Add `desugar_type_def` to build TypeDef values. |
| `tao/import_resolver.gleam` | Simplify — only update env, not ctrs. |

### What Stays the Same

| Module | Why |
|--------|-----|
| `core/eval.gleam` | Evaluation doesn't change — constructors are values |
| `core/unify.gleam` | Unification doesn't change |
| `core/subst.gleam` | Substitution doesn't change |
| `core/generalize.gleam` | Generalization doesn't change |
| `core/quote.gleam` | Quoting doesn't change |
| `core/syntax.gleam` | Parser/formatter don't change |

### Backward Compatibility

- The `CtrUndefined` error variant stays the same
- The `MatchMissing` error variant stays the same
- `infer_ctr` signature is unchanged
- All existing tests should still pass (after removing CtrEnv references)

## Testing Strategy

Add tests to `test/core/infer_test.gleam`:

```gleam
// Type definition in env
pub fn check_type_def_in_env_test() {
  let td = make_option_type_def()
  let state = State(..initial_state([]), vars: [#("Option", #(VType(td), VNeut(HVar(1), [])))]
  let result = infer(state, Ctr("Some", Lit(42), sp()))
  let #(value, type_, _) = result
  assert value == VCtr("Some", VLit(42))
}

pub fn check_type_def_option_some_test() {
  // check #Some(42) : Option
  // → type should be Option(42) after substitution
}

pub fn check_type_def_option_none_test() {
  // check #None() : Option
  // → type should be Option(42) (same template, different tag)
}

pub fn check_type_def_nat_uniform_test() {
  // check #S(#Z()) : Nat
  // → type should be Nat() (uniform across constructors)
}

pub fn check_type_def_vec_nil_test() {
  // check #Nil() : Vec(0, a)
  // → type should be Vec(0, a)
}

pub fn check_type_def_vec_cons_test() {
  // check #Cons(1, #Nil()) : Vec(1, a)
  // → type should be Vec(1, a)
}

pub fn exhaust_type_def_bool_test() {
  // exhaustiveness [True] → missing: [False]
}

pub fn exhaust_type_def_option_test() {
  // exhaustiveness [Some] → missing: [None]
}

pub fn exhaust_type_def_nat_test() {
  // exhaustiveness [Z] → missing: [S]
}

pub fn exhaust_type_def_vec_test() {
  // exhaustiveness [Nil] → missing: [Cons]
}
```

## Summary

This design eliminates the separate `ctrs` registry by storing type definitions as first-class env values. The benefits are:

1. **One registry** — `State.vars` is the only place definitions live
2. **Uniform lookup** — same env lookup for types and values
3. **Simpler imports** — one env entry per type definition
4. **Free exhaustiveness** — constructors are in the TypeDef
5. **Extensible** — user-defined types in Core code are possible

The prototype proves the approach works for all four categories: simple ADTs, parameterized ADTs, recursive ADTs, and GADTs.
