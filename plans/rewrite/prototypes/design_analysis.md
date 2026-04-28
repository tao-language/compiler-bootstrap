# Design Analysis: Type Definitions Approach

## The Core Question

How do we represent type definitions (ADTs, GADTs) in the compiler?

## Three Approaches

### A: Separate CTRs Registry (Current)

```gleam
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // regular variables
    ctrs: List(ctr_entry),                    // type constructors
    // ...
  )
}

pub type ctr_entry {
  CtrEntry(name, tag, arg_type, ret_type)
}
```

**Pros:**
- Explicit, easy to find
- Type checker can do fast lookup

**Cons:**
- Duplication: constructor info in both env AND ctrs
- Two places to update when adding a type
- Type definitions aren't first-class values
- Can't be used in expressions (can't pass `Option` as an argument)

### B: TypeDefs in Env (Proposed)

```gleam
pub type State {
  State(
    vars: List(#(String, #(Value, Value))),  // everything in one env
    // no ctrs field
  )
}

// "Option" → (TypeDef, Type) in vars
// "identity" → (VLam, VPi) in vars
// All definitions are uniform
```

**Pros:**
- One source of truth — env is the only registry
- Type definitions are first-class values
- Simple: lookup + substitute, no special cases
- Exhaustiveness is "free" — constructors are in the TypeDef
- Consistent with dependently-typed "terms == types"

**Cons:**
- Type checker needs to recognize TypeDef values
- Slightly more complex TypeDef structure

### C: Separate CtrEnv Module

```gleam
// Dedicated module for type definitions
pub type CtrEnv {
  CtrEnv(types: List(#(String, TypeDef)))
}

// Passed alongside State
pub fn check(state: State, ctr_env: CtrEnv, term: Term) -> ...
```

**Pros:**
- Clean separation of concerns
- Type checker doesn't need to recognize TypeDef values

**Cons:**
- Still two registries (vars + ctr_env)
- Import resolver needs to update both
- More arguments passed around

## Recommendation: Approach B (TypeDefs in Env)

**It is the cleanest, simplest, and most maintainable.**

### Why?

1. **Single source of truth** — Everything lives in `State.vars`
2. **Uniform env** — Regular definitions AND type definitions are the same shape
3. **Less state to thread** — No separate `ctrs` field
4. **Import is simpler** — `import std/option` just adds an env entry
5. **Extensible** — Users can define types in Core code itself

### The Minimal Implementation

```gleam
// In State, just keep vars:
pub type State {
  State(vars: List(#(String, #(Value, Value))), errors: ..., hole_counter: ...)
}

// Type definitions are stored as special values in vars:
// "Option" → (TypeDef, VNeut(HVar(0), []))

// The type checker just does:
fn lookup_type_def(env, name) -> Result(TypeDef, Error) {
  case env_lookup(env, name) {
    Ok(#(TypeDef(..), _)) -> Ok(TypeDef)
    Error(_) -> Error
  }
}
```

No separate `ctrs` field. No separate registry. Just one env.
