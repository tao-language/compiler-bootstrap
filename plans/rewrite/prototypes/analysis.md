# Summary: Type Definitions as First-Class Env Values

## What We Tested

A proof of concept (Python) demonstrating that type definitions can be
stored in the environment as regular entries instead of a separate
`ctrs` registry. Tested four types:

| Type | Category | Params | Key Property |
|------|----------|--------|-------------|
| `Bool` | Simple ADT | 0 | Basic inference + checking |
| `Option` | Parameterized ADT | 1 (a) | Type param substitution |
| `Nat` | Recursive ADT | 0 | Uniform type across constructors |
| `Vec` | Recursive GADT | 2 (n, a) | Index computation from args |

## Answers to Your Questions

### Q1: Could types be defined as a function that pattern matches on constructors?

**Yes, but with a clarification.** The "pattern matching" isn't done by
Core's `match` expression. Instead, the TypeDef **contains** the
constructor patterns as data structures. The `type_of()` function
"pattern matches" by:

1. Finding the constructor by tag (like a match on the constructor tag)
2. Returning the result type template with substituted type params

In Core terms, you could represent this as:
```
Option = $fn(a) => $fn(ctr) => $match ctr {
  #Some(_) => #Option(a)
  #None(_) => #Option(a)
}
```

When you call `Option(42)`, you get the type checker function. When you
pass a constructor to it, the match reduces and returns the type.

### Q2: Would infer on `#Some(42)` just give `#Some($Int)` without context?

**Yes, exactly.** The inferred type is a neutral placeholder `V(0)`
(HVar(0)), which means "type is at level 0 of the env." This doesn't
need to know about `Option` yet.

```
infer(#Some(42)) = (#Some(42), V(0), state)
```

### Q3: What if you try to check `#Some(42)` against `#Option($Int)`?

The flow is:

```
check(#Some(42), Option(42))
  = lookup Option in env → TypeDef
  = extract type arg = type of 42 = 42 (terms == types)
  = type_of(TypeDef, [42], "Some", [#Some(42)])
  = substitute([42], VCtr("Option", HVar(0)))
  = VCtr("Option", 42)
  = unify(VCtr("Option", 42), VCtr("Option", 42))
  = ✓
```

### Q4: Would this work for GADTs like `#Vec(n, a)`?

**Yes, but GADTs need index computation.** The difference:

| ADT (Option) | GADT (Vec) |
|---|---|
| Result template: `#Option(a)` | Result template: `#Vec(n, a)` |
| `a` comes from type args | `n` comes from **constructor args** |
| Simple substitution | Substitution + computation |

For `Vec`, the type definition stores:
```
Nil: result = #Vec(0, a)           — n is concrete 0
Cons: result = #Vec(n, a)          — n is a variable
```

When checking `Cons`:
```
Cons(x, xs): Vec(m+1, a)
  where m = index of xs: Vec(m, a)
```

The index `m` must be extracted from the **runtime value** of `xs`. In
Core, this would be:
1. Evaluate `xs` to a value
2. Look up its type in env
3. Pattern match the type to extract `m`
4. Compute `m + 1`

### Q5: For Vec, when checking `#Cons(1, #Nil())`, how does the recursive check work?

The key insight: **we don't need to recursively check `xs`.** We just
need to know `xs`'s **type** to extract its index.

```
#Cons(1, #Nil()) : Vec(1, a)

1. Infer xs = #Nil() : Vec(0, a)   ← we know this from the Vec TypeDef
2. Extract index from xs's type: m = 0
3. Cons's index = m + 1 = 1
4. Result: #Vec(1, a)
```

In Core, step 1 would be handled by the type checker. The TypeDef for
Vec tells us that `#Nil()` always has type `Vec(0, a)`, so we extract
`m = 0` directly from the TypeDef, without needing to evaluate or
recursively check.

### Q6: When unifying, we're unifying two types, and type definitions are written in terms of types, not terms.

This is a great observation. The key distinction:

- **Unification** operates on **types** (which are values in Core)
- **Type definitions** produce **types** through **substitution**

For Option:
```
Expected: #Option(a)      ← a is a type parameter
Inferred: #Option(VLit(42))  ← a is substituted with 42
Unify: #Option(a) == #Option(42) → a = 42
```

For Vec:
```
Expected: #Vec(n, a)
Inferred: #Vec(VLit(1), a)  ← n is computed from constructor args
Unify: #Vec(n, a) == #Vec(1, a) → n = 1
```

## Lessons Learned

### 1. Type params ARE type arguments to `type_of()`

```python
def type_of(td, type_args, tag, arg_values):
    # type_args: [42] for Option(42)
    # arg_values: [#Some(42)] for the constructor's runtime value
    ...
```

### 2. GADT index extraction requires env lookup

For `Cons`, we need to extract `m` from `xs`. Since `xs` has type
`Vec(m, a)` in the env, we:
1. Look up `xs`'s binding in env
2. Extract `m` from the type
3. Compute `m + 1`

### 3. Shadowing is a variable binding issue, not a fundamental problem

The "shadowing" in `#Some(a) => #Option(a)` happens because both the
type parameter and the constructor argument use the same name. In
de Bruijn encoding:
- Type param `a` = `HVar(0)` (the most recent binding)
- Constructor arg `a` = a **different** binding (the match variable)

When properly encoded with de Bruijn indices, there's no ambiguity.

### 4. Exhaustiveness is "free" from the TypeDef

Since the TypeDef stores all constructors, exhaustiveness checking is
just: "do the patterns cover all constructor tags?" No separate
registry or pass needed.

## Implementation in Core (Gleam)

Here's what the Core implementation would look like:

```gleam
// 1. TypeDef in env (same as current State.vars)
//    "Option" → (TypeDef, Type)

// 2. infer_ctr — NO CHANGES
fn infer_ctr(state, tag, arg, _) -> #(value, type, state) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  #(ctr_val, VNeut(HVar(0), []), state)  // neutral placeholder
}

// 3. check_ctr — NEW: look up TypeDef
fn check_ctr(state, tag, arg, expected) -> #(value, type, state) {
  let arg_val = evaluate(state, arg)
  let ctr_val = VCtr(tag, arg_val)
  
  case env_lookup(state, expected) {
    Ok(#(TypeDef(name, nparams, ctors), _)) ->
      case type_of_type_def(ctors, nparams, [arg_val], tag, [arg_val]) {
        Ok(ctor_type) -> {
          let state2 = unify(state, ctor_type, expected)
          #(ctr_val, ctor_type, state2)
        }
        Error(msg) -> error(state, msg)
      }
    _ -> check_without_type_def(state, tag, arg, expected)
  }
}

// 4. type_of_type_def — THE KEY FUNCTION
fn type_of_type_def(ctors, nparams, type_args, tag, arg_types) -> #(Value, Error) {
  case find_constructor(ctors, tag) {
    Ok(ctor) -> {
      let result = substitute(type_args, ctor.result)
      // For GADTs, compute indices
      case compute_gadt_indices(ctor, arg_types, type_args) {
        Ok(computed) -> #(computed, Error)
        Error(_) -> #(result, Error)
      }
    }
    Error -> #(VErr, CtrUndefined(tag, name))
  }
}

// 5. Exhaustiveness — FROM TypeDef
fn check_exhaustiveness(td, patterns) -> Result(Nil, Error) {
  let all_tags = [c.tag || c <- td.ctors]
  let missing = [t || t <- all_tags, t <> patterns]
  case missing {
    [] -> Ok(Nil)
    [_ | ..] -> Error(MatchMissing(missing, patterns))
  }
}
```

## Key Takeaways

1. **No separate `ctrs` registry needed** — TypeDefs in env are sufficient
2. **Inference stays context-free** — neutral placeholder works without context
3. **Checking uses substitution** — type params substituted via `type_of()`
4. **GADTs add computation** — index extraction from constructor arg types
5. **Exhaustiveness is built-in** — no extra pass needed
6. **Terms == types** — in dependently typed Core, the type of a value
   IS the value itself, making substitution straightforward
