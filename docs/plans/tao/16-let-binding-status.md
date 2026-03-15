# Let Binding Implementation Status

> **Status**: ✅ Parsing works, ⏳ Scoping needs fix
> **Date**: March 15, 2026

---

## Summary

Let binding **parsing** is now working correctly! The grammar successfully parses:
- `let x = 10`
- `let mut y = 20`
- `let z: Int = 30`

However, **variable scoping** is not yet implemented in the `core_term_to_term_loop` function, which causes variables to be converted with incorrect De Bruijn indices.

---

## What Works

1. ✅ **Grammar parsing**: `Let` rule correctly parses let bindings
2. ✅ **Statement conversion**: `exprs_to_stmts` converts `Let` expressions to `StmtLet`
3. ✅ **Desugaring**: `StmtLet` is desugared to `CoreLet`
4. ✅ **Sequential binding**: `build_sequential_loop` creates lambda applications

---

## What's Broken

1. ❌ **Variable scoping**: `core_term_to_term_loop` doesn't track variable scopes
2. ❌ **De Bruijn indices**: Variables are converted with index 0 instead of looking up the scope
3. ❌ **Lambda body conversion**: `CoreLam` body is converted without adding parameter to scope

---

## Root Cause

The `core_term_to_term_loop` function converts `CoreTerm` to `core/core.Term` without access to the `DesugarContext` (which tracks variable scopes). This means:

1. `CoreVar(name, span)` is converted to `Var(index: 0, span)` (always index 0)
2. `CoreLam(param, body, span)` converts the body without adding `param` to the scope
3. Variable references can't find their bindings

---

## Fix Plan

### Option 1: Pass Scope to `core_term_to_term_loop`

Add a scope parameter to `core_term_to_term_loop`:

```gleam
fn core_term_to_term_loop(term: CoreTerm, scope: List(String)) -> Term {
  case term {
    CoreVar(name, span) -> {
      let index = lookup_variable(scope, name)
      Var(index: index, span: span)
    }
    CoreLam(param, body, span) -> {
      Lam(
        param: #(param, ...),
        body: core_term_to_term_loop(body, [param, ..scope]),
        ...
      )
    }
    ...
  }
}
```

### Option 2: Use `DesugarContext` in Conversion

Pass the `DesugarContext` to the conversion function and use it for variable lookup.

### Option 3: Annotate `CoreTerm` with Indices

During desugaring, annotate variables with their De Bruijn indices, so the conversion doesn't need scope information.

---

## Files to Modify

1. `src/tao/desugar.gleam`:
   - `core_term_to_term_loop` - Add scope parameter
   - `CoreLam` case - Add parameter to scope when converting body
   - `CoreVar` case - Look up variable in scope

2. `src/tao/desugar.gleam`:
   - `desugar_module` - Pass initial scope to conversion

---

## Testing

After fixing, test with:
```tao
let x = 10
let y = 20
let z = x + y
z
```

Expected output: `30`

---

## Current Workaround

For now, examples with let bindings show `?-1` (unbound variable) to indicate the scoping issue. The parsing is correct, but evaluation fails due to the scoping bug.
