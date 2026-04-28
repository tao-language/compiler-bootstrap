# Type Definitions as First-Class Env Values

## The Core Idea

Type definitions are stored in the environment as first-class values,
just like regular `$let` bindings. Instead of having a separate `ctrs`
field in State, type definitions are regular env entries that can be
looked up, applied, and pattern-matched.

## How It Works

### 1. Inference (no context needed)

```
#Some(42)  →  #Some(42)  with type  V(0)
```

The type `V(0)` is a **neutral placeholder** — it doesn't need to know
about `Option` yet. It says "this is a constructor value; its type will
be determined by the surrounding context."

### 2. Checking (with context)

```
check(#Some(42), Option)
```

The type checker:
1. Looks up `Option` in the env → gets the TypeDef
2. Extracts the type of `42` → `VLit(42)`
3. Substitutes this into the Option constructor's result template
4. Returns `#Option(42)` — the type is resolved

### 3. Exhaustiveness (free from the type definition)

The TypeDef's constructors ARE the exhaustive list. No separate registry
needed.

## Four Test Cases

| Type | Category | Parameters | Key Property |
|------|----------|-----------|-------------|
| `Bool` | Simple ADT | 0 | Uniform type across constructors |
| `Option` | Parameterized ADT | 1 (a) | Type param substitution |
| `Nat` | Recursive ADT | 0 | Constructor with recursive arg |
| `Vec` | Recursive GADT | 2 (n, a) | Index computation from args |

## Lessons Learned

### Lesson 1: Type parameters ARE type arguments to `type_of()`

```python
def type_of(td, args, tag, arg_vals):
    # args = type arguments (e.g., [42] for Option)
    # arg_vals = runtime constructor arguments (e.g., [VLit(42)])
    ...
```

The `type_args` list is used for **substitution**: HVar(level) is
replaced with `args[level]`. This works for both ADTs and GADTs.

### Lesson 2: `type_of` is a pure computation, not pattern matching

The type definition doesn't "pattern match" in the Core sense. Instead,
`type_of` is a function that:
1. Finds the constructor by tag
2. Returns the result type template with substituted type params
3. For GADTs, also computes indices from constructor arg types

### Lesson 3: GADT index extraction requires term-level computation

For `Vec(m+1, a)`, we need to extract `m` from `xs: Vec(m, a)`. This
requires looking at the runtime value's type and computing. In Core,
this would be:
1. Evaluate `xs` to a value
2. Pattern match on its type to extract `m`
3. Compute `m + 1`

### Lesson 4: Shadowing is just a variable binding issue

The "shadowing" problem in `#Some(a) => #Option(a)` is simply that
`a` refers to different things. In de Bruijn encoding:
- Outer `a` (type param) = HVar(1)
- Inner `a` (constructor arg) = HVar(0)

These are distinct. The template `VCtr("Option", HVar(0))` correctly
references the type param, not the constructor arg.

### Lesson 5: Exhaustiveness comes "for free" from the TypeDef

Since the TypeDef stores all constructors, checking exhaustiveness is
just: "do the patterns cover all constructor tags?" No separate registry
is needed.

## Implementation Plan for Core

### Step 1: Add TypeDef to env

```gleam
// In core/ast.gleam, the env already has:
// List(#(String, #(Value, Value)))

// Type definitions are stored as:
// "Option" → (TypeDef, Type)
// where TypeDef is a special Value that the type checker recognizes
```

### Step 2: Update `infer_ctr`

Current:
```gleam
fn infer_ctr(state, tag, arg, _) -> #(value, type, state) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  #(ctr_val, VNeut(HVar(0), []), state)
}
```

This stays the same — no changes needed!

### Step 3: Update `check_ctr`

```gleam
fn check_ctr(state, tag, arg, expected) -> #(value, type, state) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  
  // Look up expected type in env
  case env_lookup(state.env, expected_name) {
    Ok(#(value, _)) -> case value {
      TypeDef(name, nparams, constructors) -> {
        // Get type of constructor arg for substitution
        let arg_type = arg_val
        
        // Compute constructor type
        case type_of_td(constructors, [arg_type], tag, [arg_val]) {
          Ok(ctor_type) -> {
            // Unify
            let state2 = unify(state, ctor_type, expected)
            #(ctr_val, ctor_type, state2)
          }
          Error(msg) -> error(state, msg)
        }
      }
      _ -> // Not a type def, fall back to basic checking
    }
    Error -> // Not found, error
  }
}
```

### Step 4: Implement `type_of_td`

```gleam
fn type_of_td(constructors, type_args, tag, arg_types) -> #(Value, Error) {
  case find_ctor(constructors, tag) {
    Ok(ctor) -> {
      let result = substitute(type_args, ctor.result_type)
      case type_of_td_computed(td_name, ctor, arg_types, type_args) {
        Ok(computed) -> #(computed, Error)
        Error(_) -> #(result, Error)
      }
    }
    Error -> #(VErr, CtrUndefined(tag, name))
  }
}
```

### Step 5: GADT index computation

```gleam
fn type_of_td_computed(td_name, ctor, arg_types, type_args) -> Value {
  case td_name {
    "Vec" -> vec_type(ctor, arg_types, type_args)
    _ -> type_args  // ADTs: no computation
  }
}

fn vec_type(ctor, arg_types, type_args) -> Value {
  case ctor.tag {
    "Nil" -> VCtr("Vec", [VLit(0), list.drop(type_args, 1)])
    "Cons" -> {
      let xs = list.drop(arg_types, 1)
      let m = extract_index(xs)  // Extract m from Vec(m, a)
      let a = list.drop(type_args, 1)
      VCtr("Vec", [compute_index(m), a])  // m + 1
    }
    _ -> type_args
  }
}

fn extract_index(xs: Value) -> Value {
  // Pattern match on xs's type to extract the index
  // In Core, xs's type would be Vec(m, a)
  // We extract m by pattern matching
}
```

### Step 6: Exhaustiveness

```gleam
fn check_exhaustiveness(td, patterns) -> Result(Nil, Error) {
  let all_tags = [c.tag || c <- td.constructors]
  let missing = [t || t <- all_tags, t <> patterns]
  case missing {
    [] -> Ok(Nil)
    [_ | ..] -> Error(MatchMissing(missing, patterns))
  }
}
```

## Why This Approach Works

1. **Type definitions are first-class**: They're stored in the env like
   any other definition. No special `ctrs` registry needed.

2. **Inference is context-free**: `#Some(42)` can be inferred without
   knowing about `Option`. The type is a neutral placeholder.

3. **Checking uses substitution**: The type definition's result template
   is a value with HVar references. Substitution resolves these.

4. **GADTs add computation**: Type param substitution + index computation
   from constructor arg types.

5. **Exhaustiveness is built-in**: The TypeDef's constructors ARE the
   exhaustive list. No separate data structure.

## Key Differences from Traditional Approaches

| Aspect | Traditional | This Approach |
|--------|------------|---------------|
| Storage | Separate `ctrs` table | Regular env entries |
| Inference | Needs ctr lookup | Context-free (neutral placeholder) |
| Checking | Unification against ctr type | Substitution + unification |
| GADTs | Special index extraction | Computation from arg types |
| Exhaustiveness | Separate pass | Extract from TypeDef |
