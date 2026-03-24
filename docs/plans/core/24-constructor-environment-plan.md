# Constructor Environment for Exhaustiveness Checking - Implementation Plan

> **Date**: March 2026 (Updated)
> **Status**: 📝 Planning
> **Goal**: Populate State.ctrs from Tao type definitions (no hardcoded prelude)

---

## Architecture Principle

**State should NOT have hardcoded constructor definitions.** Constructor definitions should be derived from Tao's type definitions in the source code.

### Why No Hardcoded Prelude?

1. **Separation of concerns**: The core language shouldn't know about specific types
2. **Testability**: Examples should define their own types, not rely on prelude
3. **Correctness**: The prelude should be written in Tao, not hardcoded in Gleam
4. **Bootstrapping**: We need the language to work before writing the prelude

### Correct Flow

```
Tao Source → Parse → Tao AST → Desugar → Core Term → Type Check
                ↓                        ↑
          Type Definitions        State.ctrs populated
          (type T = A | B)        from Tao type defs
```

---

## Implementation Plan

### Step 1: Remove Hardcoded Prelude from core.gleam

**File**: `src/core/core.gleam`

Remove `prelude_ctrs` constant and use empty list:

```gleam
/// Initial state with empty constructor environment.
/// Constructors are populated from Tao type definitions during desugaring.
pub const initial_state = State(
  hole: 0,
  var: 0,
  ctrs: [],  // Empty - populated from Tao type definitions
  ctx: [],
  sub: [],
  errors: [],
  ffi: ffi_build,
  config: default_config,
)
```

### Step 2: Add Type Definition Support to Tao AST

**File**: `src/tao/ast.gleam`

Add `StmtType` for type definitions:

```gleam
/// type Name(params) = Constructor1 | Constructor2 | ...
StmtType(
  name: String,
  type_params: List(String),
  constructors: List(Constructor),
  span: Span,
)

pub type Constructor {
  Constructor(
    name: String,
    fields: List(#(Option(String), Type)),  // Optional field name, type
    span: Span,
  )
}
```

### Step 3: Parse Type Definitions

**File**: `src/tao/syntax.gleam`

Add grammar rule for type definitions:

```gleam
// Type = "type" Ident ["(" Ident ("," Ident)* ")"] "=" Constructor ("|" Constructor)*
rule("Type", [
  seq([
    keyword_pattern("type"),
    token_pattern("Ident"),  // type name
    opt(seq([
      token_pattern("LParen"),
      token_pattern("Ident"),  // type param
      many(seq([token_pattern("Comma"), token_pattern("Ident")])),
      token_pattern("RParen"),
    ])),
    token_pattern("Equal"),
    ref("Constructor"),
    many(seq([token_pattern("Pipe"), ref("Constructor")])),
  ]),
  fn(values) { ... make_type_def(values) },
])
```

### Step 4: Collect Type Definitions During Desugaring

**File**: `src/tao/desugar.gleam`

Add `ctrs` field to `DesugarContext` and populate from type definitions:

```gleam
pub type DesugarContext {
  DesugarContext(
    global: GlobalContext,
    current_module: String,
    local_scope: List(String),
    loop_stack: List(LoopInfo),
    ctrs: CtrEnv,  // Populated from Tao type definitions
  )
}

pub fn desugar_module(module: Module, ctx: GlobalContext) -> #(Term, DesugarContext) {
  // Start with empty ctrs
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
    loop_stack: [],
    ctrs: [],
  )
  
  // Process type definitions first to populate ctrs
  let dc_with_types = process_type_definitions(module.body, dc)
  
  // Then desugar rest of module with populated ctrs
  desugar_stmts(module.body, dc_with_types)
}

fn process_type_definitions(stmts: List(Stmt), dc: DesugarContext) -> DesugarContext {
  list.fold(stmts, dc, fn(acc_dc, stmt) {
    case stmt {
      StmtType(name, type_params, constructors, _span) => {
        // Convert Tao type definition to Core CtrDef entries
        let new_ctrs = tao_type_to_core_ctrs(name, type_params, constructors)
        DesugarContext(..acc_dc, ctrs: list.append(acc_dc.ctrs, new_ctrs))
      }
      _ => acc_dc
    }
  })
}
```

### Step 5: Convert Tao Type to Core CtrDef

**File**: `src/tao/desugar.gleam`

```gleam
fn tao_type_to_core_ctrs(
  type_name: String,
  type_params: List(String),
  constructors: List(Constructor),
) -> CtrEnv {
  list.map(constructors, fn(ctr) {
    let ctr_def = CtrDef(
      type_params: type_params,
      field_types: extract_field_types(ctr.fields),
      return_type: build_return_type(type_name, type_params),
    )
    #(ctr.name, ctr_def)
  })
}
```

### Step 6: Pass ctrs to Type Checking

**File**: `src/compiler_bootstrap.gleam` or wherever type checking is invoked

When creating the initial State for type checking, use ctrs from desugaring:

```gleam
// After desugaring
let #(term, dc) = desugar_module(module, ctx)

// Create state with ctrs from desugaring
let initial_state_with_ctrs = core.State(
  hole: 0,
  var: 0,
  ctrs: dc.ctrs,  // Use ctrs from Tao type definitions
  ctx: [],
  sub: [],
  errors: [],
  ffi: core.ffi_build,
  config: core.default_config,
)

// Run type checking
let #(_type_result, _type_annotation, final_state) = core.infer(initial_state_with_ctrs, term)
```

---

## Example: User-Defined Type

```tao
// Define a simple enum type
type Option(a) = Some(a) | None

// Use it with pattern matching
let x = Some(42)
match x {
  | Some(v) -> v
  | None -> 0
}
```

This should:
1. Parse the type definition
2. Create CtrDef entries for `Some` and `None`
3. Populate `State.ctrs` with these definitions
4. Type checking recognizes `Some` + `None` as exhaustive for `Option`

---

## Testing Strategy

### Test 1: Simple Enum

```tao
type Color = Red | Green | Blue

let c = Red
match c {
  | Red -> 1
  | Green -> 2
  | Blue -> 3
}
```

Expected: No exhaustiveness errors

### Test 2: Missing Constructor

```tao
type Color = Red | Green | Blue

let c = Red
match c {
  | Red -> 1
  | Green -> 2
}
```

Expected: "Pattern match not exhaustive - missing Blue"

### Test 3: Polymorphic Type

```tao
type Option(a) = Some(a) | None

let x = Some(42)
match x {
  | Some(v) -> v
  | None -> 0
}
```

Expected: No exhaustiveness errors

---

## Files to Modify

1. **`src/core/core.gleam`** - Remove `prelude_ctrs`, use empty list
2. **`src/tao/ast.gleam`** - Add `StmtType` and `Constructor` types
3. **`src/tao/syntax.gleam`** - Add type definition grammar
4. **`src/tao/desugar.gleam`** - Add `ctrs` field, process type definitions
5. **`src/compiler_bootstrap.gleam`** - Pass ctrs from desugaring to type checking
6. **`examples/tao/programs/`** - Update examples to define their own types

---

## Migration Path

### Current State

- `core.gleam` has hardcoded `prelude_ctrs` with Bool, Option, Result, etc.
- Examples rely on these hardcoded definitions
- Constructor pattern exhaustiveness doesn't work

### After Fix

- `core.gleam` has empty `ctrs`
- Examples define their own types
- Constructor pattern exhaustiveness works from Tao type definitions

### Future: Prelude

Once the language works correctly:
1. Write prelude in Tao (`lib/prelude/option.tao`, etc.)
2. Auto-import prelude modules
3. Prelude types become available automatically

---

## Related Documents

- **[docs/plans/core/23-pattern-exhaustiveness-final-fix.md](./23-pattern-exhaustiveness-final-fix.md)** - Wildcard/variable fix
- **[docs/plans/core/25-pattern-exhaustiveness-status.md](./25-pattern-exhaustiveness-status.md)** - Current status
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core language
- **[src/tao/desugar.gleam](../../src/tao/desugar.gleam)** - Tao to Core desugaring
