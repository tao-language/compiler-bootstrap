# Import Design for Type Definitions in Env

## The Problem

When `main.tao` imports `std/option.tao`:
```gleam
// main.tao
import std/option

let x: option.Option(Int) = option.Some(42)
```

How does the import resolver add the type definition to the env,
and how does the qualified name `option.Option` work?

## Key Design Decisions

### 1. Type Definitions Live in the Env

When `std/option.tao` is compiled, its type definitions become env
entries:
```
"Option" → (TypeDef("Option", nparams=1, ctgs=[Some, None]), Type)
```

### 2. Qualified Names via Import Alias

```gleam
import std/option          // alias: "option"
import std/option, {Option} // alias: "option", name: "Option"
```

The import resolver creates env entries with **qualified names**:
```
"option.Option" → (TypeDef, Type)
```

### 3. The Env Structure

```
State.vars:
  [
    #("option.Option", #(TypeDef, Type)),
    #("option.Some", #(Some_value, Some_type)),
    #("option.None", #(None_value, None_type)),
  ]
```

Wait, should constructors be in the env too? **No.**

Constructors are NOT stored as env entries. Only the TYPE DEFINITION is.
Constructors are metadata within the TypeDef:
```
"option.Option" → (TypeDef { ctgs = [Some, None] }, Type)
```

When checking `#Some(42)` against `option.Option(a)`:
1. Look up `option.Option` in env → get TypeDef
2. TypeDef tells us `Some` is a valid constructor
3. Substitution computes the result type

### 4. What Gets Added to the Env

| Item | In Env? | Why |
|------|---------|-----|
| Type definition (e.g., `Option`) | YES | Needed for type checking |
| Value constructor (e.g., `#Some`) | NO | Constructor tags, not env names |
| Type-level value of constructor | Maybe | Could be stored, but not needed |
| Type definition's type | YES | So you can write `Option : $Type` |

### 5. The Import Resolver Flow

```
parse("import std/option")
  → import_item = Import("std/option", [], "option")
  
load_module("std/option")
  → module_defs = [TypeDef("Option", ctgs=[Some, None]), ...]
  
add_to_env(env, module_defs, alias="option")
  → env = [
      #("option.Option", #(TypeDef(...), Type)),
      #("option.Some_value", #(Some_value, ...)),
      #("option.None_value", #(None_value, ...)),
    ]
```

**Wait** — should we add constructor VALUES to the env? For example:
```
"option.Some" → (Some_value, Some_type)
```

This would allow writing `option.Some(42)` in expressions. But the
current system uses `#Some(42)` syntax, which doesn't need the env.

**Decision: Only add type definitions, not constructors.**

Why? Because:
- Constructors are accessed via `#Tag(arg)` syntax, not `name(arg)`
- If users want `Some(42)`, they can define `let Some = #Some` in their code
- Keeping only type defs in env is simpler

### 6. Multi-module Compilation

```
std/option.tao:
  type Option(a) { Some(a), None }

std/list.tao:
  import std/option
  type List(a) { Nil, Cons(a, List(a)) }

main.tao:
  import std/option
  import std/list
  let x: list.List(option.Option(Int)) = list.Cons(option.Some(42), list.Nil)
```

The compilation pipeline:

```
1. Compile std/option.tao
   → env_option = [("Option", TypeDef(...))]

2. Compile std/list.tao (with env_option as base)
   → env_list = [("Option", TypeDef(...)), ("List", TypeDef(...))]

3. Compile main.tao (with env_list as base)
   → env_main = [("Option", TypeDef(...)), ("List", TypeDef(...))]
```

Each module's env builds on the previous, creating a chain.

### 7. Import Variants

```gleam
// Full module import — everything available
import std/option
// Use: option.Option, option.Some

// Selective import — only specific names
import std/option, {Option}
// Use: Option (not option.Option)

// Wildcard import — all names
import std/option
// Use: Option (unqualified)
```

### 8. What Each Import Variant Produces

| Variant | Env Entry | Usage |
|---------|-----------|-------|
| `import std/option` | `"option.Option" → TypeDef` | `option.Option` |
| `import std/option, {Option}` | `"Option" → TypeDef` | `Option` |
| `import std/option` (unqualified) | `"Option" → TypeDef` | `Option` |

## Implementation Sketch

```gleam
// In import_resolver.gleam
fn add_type_defs_to_env(
  env: State,
  module_defs: List(TypeDef),
  module_alias: String,
  selective: List(String),
) -> State {
  list.fold(module_defs, env, fn(acc_env, td) {
    let qualified_name = if module_alias == "" {
      td.name
    } else {
      module_alias <> "." <> td.name
    }
    
    // Check if this is in the selective list
    case selective {
      [] -> true  // wildcard: add all
      names -> td.name in names
    } {
      True -> state.def_var(acc_env, qualified_name, td, make_type_value(td))
      False -> acc_env  // not selected, skip
    }
  })
}

fn make_type_value(td: TypeDef) -> Value {
  // The "type" of a TypeDef is $Type (type universe)
  // For parametric types: $fn(a: $Type) => $Type
  case td.nparams {
    0 -> VNeut(HVar(1), [])  // just $Type
    _ -> VPi(..., ...)  // dependent function type
  }
}
```

## Summary

1. **Only type definitions go in the env** — not constructors
2. **Qualified names follow the import alias** — `module.TypeName`
3. **Selective imports control visibility** — only selected names added
4. **Constructor resolution is by tag** — `#Some` found via TypeDef
5. **No duplication** — one env, one source of truth
