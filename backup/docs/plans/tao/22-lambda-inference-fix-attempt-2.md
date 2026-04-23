# Lambda Inference Hole Generalization Fix - Attempt 2

> **Date**: March 2026
> **Status**: 🚧 **Partial Fix** - Infrastructure in place, but hole substitution still failing

---

## Problem

The `InfiniteType` error persists even after fixing `generalize_holes` to accept `Value` for the codomain:

```
InfiniteType(4, VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
  VPi([], "_", [VNeut(HVar(1), []), VNeut(HVar(0), [])], 
    VNeut(HHole(4), []), Hole(5, ...)), Hole(3, ...)))
```

The inner `VPi` still contains `VNeut(HHole(4), [])` in its domain, indicating that Hole(4) was not substituted during generalization.

## Analysis

### Expected Flow

1. Outer lambda (`fn(a) { inner_lambda }`) creates Hole(4) for parameter `a`
2. Inner lambda (`fn(b) { body }`) creates Hole(5) for parameter `b`
3. Body is inferred, returning `body_ty` (type of inner lambda)
4. Outer lambda collects holes: `domain_holes = [4]`, `codomain_holes = [5, ...]`
5. Outer lambda generalizes: Hole(4) → HVar(0), Hole(5) → HVar(1)
6. Outer lambda's type: `VPi(HVar(0), VPi(HVar(1), Bool))`

### Actual Flow

The error shows that Hole(4) is NOT substituted. The inner `VPi` (which should be `VPi(HVar(1), Bool)`) still has `HHole(4)` in its domain.

### Possible Causes

1. **Hole(4) not in `holes_to_generalize`**: The filtering might be excluding Hole(4)
2. **Substitution not applied to correct value**: The `subst_value_with_hole_vars` might not be reaching the inner `VPi`
3. **Type structure mismatch**: The error might be showing a different type than expected

### Investigation

Looking at the error structure:
- Outer `VPi` has `env=[HVar(1), HVar(0)]` (generalized implicit params)
- Outer `VPi`'s `in_val` is another `VPi` (unexpected!)
- Inner `VPi` has `in_val=VNeut(HHole(4), [])` (not generalized!)

This suggests that the outer lambda's type is being constructed with the wrong structure. The outer lambda's `in_val` should be `HVar(0)` (the type of parameter `a`), not another `VPi`.

### Hypothesis

The error might be showing the type of the `Fix` (the `xor` function), not the outer lambda. The `Fix` type is inferred by `infer(Fix)`, which creates a hole and checks the body against it.

During `infer(Fix)`:
1. Create Hole(3) for result type
2. Add `xor : Hole(3)` to context
3. Check body (the outer lambda) against Hole(3)
4. Unify outer lambda's type with Hole(3)

The unification might be creating the strange type structure shown in the error.

## Fix Attempt

### Change 1: `generalize_holes` accepts `Value` for codomain

Modified `generalize_holes` to:
- Accept `codomain: Value` instead of `codomain: Term`
- Substitute holes in the `Value` before quoting
- This ensures nested lambda types are properly substituted

### Change 2: `infer(Lam)` passes `body_ty` instead of quoted term

Modified `infer(Lam)` to:
- Collect holes from `body_ty` (Value) instead of `t2_pre` (Term)
- Pass `body_ty` to `generalize_holes`
- This ensures hole collection is consistent with substitution

### Result

The fix is correct in principle, but the `InfiniteType` error persists. This suggests there's another issue causing Hole(4) to remain unsubstituted.

## Next Steps

### Immediate

1. **Add debug output** to trace hole collection and substitution
2. **Verify `holes_to_generalize`** includes Hole(4)
3. **Check `subst_value_with_hole_vars`** is reaching the inner `VPi`

### Medium Term

1. **Simplify the test case** to isolate the issue
2. **Add unit tests** for hole generalization
3. **Consider alternative approaches** (e.g., defer type computation for nested lambdas)

### Long Term

1. **Refactor lambda type storage** to keep types with values
2. **Implement proper dependent type support** with correct hole management
3. **Add comprehensive test suite** for type inference edge cases

---

## Code Changes

### `generalize_holes` Function

```gleam
fn generalize_holes(
  holes: List(Int),
  existing_implicit: List(String),
  domain: Value,
  codomain: Value,  // Changed from Term to Value
  s: State,
  ffi: FFI,
  lvl: Int,
  span: Span,
) -> #(List(String), Value, Term) {
  case holes {
    [] -> #(existing_implicit, domain, quote(ffi, lvl, codomain, span))
    _ -> {
      let codomain_term = quote(ffi, lvl, codomain, span)
      let existing_names = collect_existing_names(existing_implicit, codomain_term)
      let new_names = generate_unique_names(list.length(holes), existing_names, 0)
      let base_index = list.length(existing_implicit)
      let hole_subst = create_hole_to_var_subst(holes, base_index)
      
      // Apply substitution to domain and codomain (both Values)
      let generalized_domain = subst_value_with_hole_vars(hole_subst, domain)
      let generalized_codomain_val = subst_value_with_hole_vars(hole_subst, codomain)
      let generalized_codomain = quote(ffi, lvl, generalized_codomain_val, span)
      
      #(list.append(existing_implicit, new_names), generalized_domain, generalized_codomain)
    }
  }
}
```

### `infer(Lam)` Function

```gleam
Lam(implicit, param, body, span) -> {
  let #(name, _) = param
  let env = get_env(s)
  let holes_before = s.hole
  let #(t1_hole, s) = new_hole(s)
  let #(_fresh, s) = def_var(s, name, t1_hole)
  let #(body_val, body_ty, s) = infer(s, body)

  // Collect free holes from both domain and codomain (both Values)
  let domain_holes = free_holes_in_value(s.sub, t1_hole)
  let codomain_holes = free_holes_in_value(s.sub, body_ty)  // Changed from free_holes_in_term_direct(t2_pre)
  let all_holes = list.unique(list.append(domain_holes, codomain_holes))

  let holes_to_generalize = list.filter(all_holes, fn(id) { id >= holes_before })

  // Pass body_ty (Value) instead of quoted term
  let #(generalized_implicit, generalized_t1, generalized_t2) =
    generalize_holes(holes_to_generalize, implicit, t1_hole, body_ty, s, s.ffi, list.length(env), span)

  let body_quoted = quote(s.ffi, list.length(env), body_val, span)

  #(VLam(implicit, name, env, body_quoted), VPi(generalized_implicit, name, env, generalized_t1, generalized_t2), s)
}
```

---

## Test Results

| Test | Status | Notes |
|------|--------|-------|
| `lib_prelude_bool_module_test` | ❌ FAIL | InfiniteType error persists |
| `core examples` | ⚠️ MIXED | 1 failure (pattern mismatch) |
| `tao examples` | ⚠️ MIXED | 3 failures |
| **Total** | **519 passed, 5 failures** | Same as before fix |

---

## Related Documents

- **[20-type-annotations-root-cause.md](20-type-annotations-root-cause.md)** - Root cause analysis
- **[21-type-annotations-final-analysis.md](21-type-annotations-final-analysis.md)** - Previous analysis
- **[19-type-annotations-fix.md](19-type-annotations-fix.md)** - Main implementation plan
