# Constructor Environment for Exhaustiveness Checking - Implementation Plan

> **Date**: March 2026
> **Status**: 📝 Planning
> **Goal**: Populate State.ctrs during Tao→Core conversion for proper exhaustiveness checking

---

## Problem

The exhaustiveness checker in `core.gleam` uses `State.ctrs` (constructor environment) to determine which constructors belong to which types. Currently, `State.ctrs` only contains hardcoded prelude types (Bool, Option, Result, Ordering, List).

When checking constructor patterns like:
```tao
match opt {
  | Some(x) -> x
  | None -> 0
}
```

The exhaustiveness checker doesn't know that `Some` and `None` are the only constructors of `Option`, so it reports "Pattern match not exhaustive".

## Solution

Populate `State.ctrs` with constructor definitions during Tao→Core conversion. Since Tao doesn't have user-defined type definitions yet, we'll:

1. **Extend prelude types**: Add more constructor definitions to `core.gleam`'s `prelude_ctrs`
2. **Pass ctrs through DesugarContext**: Thread the constructor environment through the desugaring process
3. **Initialize State with ctrs**: When creating the initial State for type checking, include the constructor definitions

---

## Implementation Plan

### Step 1: Extend DesugarContext with ctrs field

**File**: `src/tao/desugar.gleam`

Add a `ctrs` field to `DesugarContext` to track constructor definitions:

```gleam
pub type DesugarContext {
  DesugarContext(
    global: GlobalContext,
    current_module: String,
    local_scope: List(String),
    loop_stack: List(LoopInfo),
    ctrs: CtrEnv,  // NEW: Constructor definitions
  )
}
```

### Step 2: Initialize ctrs in desugar_module

**File**: `src/tao/desugar.gleam`

Initialize `DesugarContext` with prelude constructors:

```gleam
pub fn desugar_module(module: Module, ctx: GlobalContext) -> #(Term, DesugarContext) {
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
    loop_stack: [],
    ctrs: core_prelude_ctrs,  // Import from core
  )
  ...
}
```

### Step 3: Export prelude_ctrs from core.gleam

**File**: `src/core/core.gleam`

Make `prelude_ctrs` public so it can be imported:

```gleam
pub const prelude_ctrs = [
  #("True", CtrDef([], Typ(0, no_span), Typ(0, no_span))),
  #("False", CtrDef([], Typ(0, no_span), Typ(0, no_span))),
  #("Some", CtrDef(["a"], Var(0, no_span), Typ(0, no_span))),
  #("None", CtrDef(["a"], Typ(0, no_span), Typ(0, no_span))),
  ...
]
```

### Step 4: Use ctrs in type checking

**File**: `src/tao/compiler.gleam` or wherever type checking is invoked

When creating the initial State for type checking, include the ctrs:

```gleam
let initial_state = core.initial_state(
  hole: 0,
  var: 0,
  ctrs: dc.ctrs,  // Use ctrs from desugaring
  ctx: [],
  sub: [],
  errors: [],
  ffi: core.ffi_build,
  config: core.default_config,
)
```

---

## Alternative: Simpler Approach

Since Tao doesn't have user-defined types yet, we can simply ensure the prelude ctrs are used:

1. Keep `prelude_ctrs` in `core.gleam` (already done)
2. Ensure `initial_state` uses `prelude_ctrs` (already done)
3. The issue might be that the State isn't being passed correctly to the exhaustiveness checker

Let me investigate where the State is created for type checking...

---

## Investigation Findings

Looking at the code:

1. `core.initial_state` already uses `prelude_ctrs` ✅
2. The exhaustiveness checker uses `s.ctrs` from the State ✅
3. The issue might be in how the State is created during type checking

Need to trace where the State is created for type checking match expressions...

---

## Next Steps

1. Trace State creation in type checking
2. Verify ctrs is being passed correctly
3. Test with constructor patterns
4. Document findings

---

## Related Documents

- **[docs/plans/core/23-pattern-exhaustiveness-final-fix.md](./23-pattern-exhaustiveness-final-fix.md)** - Previous fix summary
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language with exhaustiveness checking
- **[src/tao/desugar.gleam](../../src/tao/desugar.gleam)** - Tao to Core desugaring
