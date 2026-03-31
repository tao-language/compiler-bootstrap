# Lambda Generalization Fix: Option A - Absolute HVar Indices

**Date**: March 31, 2026  
**Status**: Root Cause Identified - Fix Planned  
**Current State**: 526 tests passing, 7 failures

---

## Executive Summary

The lambda generalization bug is caused by **relative HVar indices** that collide when nested lambdas are generalized. The fix is to modify `quote_domain_with_implicit` to create **absolute HVar indices** that track the total number of implicit parameters from all outer scopes.

---

## Root Cause Analysis

### The Bug

When generalizing nested lambdas like `k = x -> y -> x`:

1. **During generalization** (`generalize_holes`):
   ```
   holes = [h1, h2]
   hole_subst = [(h1, 0), (h2, 1)]
   
   // After subst_value_with_hole_vars (NO SHIFT):
   VPi(["_0"], "x", _, HVar(0), VPi(["_0"], "y", _, HVar(0), Var(1)))
   //                                    ^^^^ Should be HVar(1) after shift!
   ```

2. **During application** (`infer_app`):
   ```
   implicit_subst = [(0, h1)]  // Only outer implicit instantiated
   
   // Both HVar(0) match (0, h1):
   VPi(["_0"], "x", _, HHole(h1), VPi(["_0"], "y", _, HHole(h1), Var(1)))
   // Inner implicit never gets its own hole!
   ```

### Why Current Code Fails

The `subst_value_with_hole_vars` function does NOT shift when entering binders:

```gleam
fn subst_value_with_hole_vars(subst, value) -> Value {
  case value {
    VPi(impl, name, env, in_val, out) ->
      VPi(impl, name, env,
        subst_value_with_hole_vars(subst, in_val),  // NO SHIFT!
        subst_term_with_hole_vars(subst, out),      // NO SHIFT!
      )
  }
}
```

---

## Option A: Absolute HVar Indices

### Core Idea

Modify `quote_domain_with_implicit` to track an **offset** representing the total number of implicit parameters from outer scopes. HVar indices become **absolute positions** in the combined context.

### Implementation

#### Step 1: Add Offset Parameter to `quote_domain_with_implicit`

```gleam
fn quote_domain_with_implicit(
  ffi: FFI,
  num_implicit: Int,
  value: Value,
  s: Span,
  steps: Int,
  offset: Int,  // NEW: absolute position offset
) -> Term {
  case steps {
    0 -> Hole(-1, s)
    _ -> quote_domain_with_implicit_loop(ffi, num_implicit, value, s, steps, offset)
  }
}

fn quote_domain_with_implicit_loop(
  ffi: FFI,
  num_implicit: Int,
  value: Value,
  s: Span,
  steps: Int,
  offset: Int,
) -> Term {
  case value {
    // ... other cases ...
    
    VPi(impl, name, env, in_val, out_term) -> {
      // Domain uses current offset (references outer implicit params)
      let in_quote = quote_domain_with_implicit(ffi, num_implicit, in_val, s, steps - 1, offset)
      
      // For codomain, increase offset by THIS VPi's implicit params + 1 for the binder
      let new_offset = offset + list.length(impl) + 1
      let fresh = VNeut(HVar(new_offset), [])
      let out_quote = quote_term_in_env(
        ffi, new_offset, out_term, [fresh, ..env], get_span(out_term), steps - 1)
      
      Pi(impl, name, in_quote, out_quote, s)
    }
    
    VLam(impl, name, env, body) -> {
      // Similar to VPi but for VLam
      let new_offset = offset + list.length(impl) + 1
      let fresh = VNeut(HVar(new_offset), [])
      let body_quote = quote_term_in_env(
        ffi, new_offset, body, [fresh, ..env], get_span(body), steps - 1)
      let param_ty_quote = quote_domain_with_implicit(ffi, num_implicit, fresh, s, steps - 1, offset)
      Lam(impl, #(name, param_ty_quote), body_quote, s)
    }
    
    // ... other cases ...
  }
}
```

#### Step 2: Update `quote_domain_head`

```gleam
fn quote_domain_head(num_implicit: Int, head: Head, s: Span, offset: Int) -> Term {
  case head {
    HVar(l) -> Var(l + offset, s)  // Absolute position
    HHole(id) -> Hole(id, s)
    HStepLimit -> Hole(-1, s)
  }
}
```

#### Step 3: Update `generalize_holes`

```gleam
fn generalize_holes(holes, existing_implicit, domain, codomain, s, ffi, lvl, span) {
  let base_index = list.length(existing_implicit)
  let hole_subst = create_hole_to_var_subst(holes, base_index)
  
  // Substitute with offset 0 (no outer implicit params yet)
  let generalized_domain = subst_value_with_hole_vars_shifted(hole_subst, domain, 0)
  
  case holes {
    [] -> #(existing_implicit, generalized_domain, quote(ffi, lvl, codomain, span))
    _ -> {
      let codomain_term = quote(ffi, lvl, codomain, span)
      let existing_names = collect_existing_names(existing_implicit, codomain_term)
      let new_names = generate_unique_names(list.length(holes), existing_names, 0)
      
      // Substitute with offset 0
      let generalized_codomain_val = subst_value_with_hole_vars_shifted(hole_subst, codomain, 0)
      
      // Quote with offset = number of NEW implicit params
      let num_new_implicit = list.length(holes)
      let generalized_codomain = quote_domain_with_implicit(
        ffi, num_new_implicit, generalized_codomain_val, span, 100_000, 0)
      
      #(list.append(existing_implicit, new_names), generalized_domain, generalized_codomain)
    }
  }
}
```

#### Step 4: Add Shifted Hole Substitution

```gleam
fn subst_value_with_hole_vars_shifted(
  subst: List(#(Int, Int)),
  value: Value,
  shift: Int,
) -> Value {
  case value {
    VNeut(HHole(id), []) -> {
      case list.key_find(subst, id) {
        Ok(index) -> VNeut(HVar(index + shift), [])  // Add shift to index
        Error(Nil) -> value
      }
    }
    VPi(impl, name, env, in_val, out) -> {
      let new_shift = shift + list.length(impl)
      VPi(impl, name, env,
        subst_value_with_hole_vars_shifted(subst, in_val, new_shift),
        subst_term_with_hole_vars_shifted(subst, out, new_shift),
      )
    }
    // ... other cases with shift ...
  }
}
```

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/core/core.gleam` | Add offset parameter to quoting functions, add shifted substitution |
| `test/core/hvar_fix_test.gleam` | Keep as regression tests |
| `docs/tao-lambda-generalization.md` | Update with fix details |

---

## Test Plan

### Unit Tests (Already Created)

1. **`k_combinator_type_structure_test`** - Verify nested lambda type structure
2. **`k_combinator_application_test`** - Verify `k(10)(20) = 10`
3. **`church_numeral_zero_test`** - Verify `zero = f -> x -> x` type-checks
4. **`compose_combinator_test`** - Verify triple-nested lambda
5. **`church_numeral_succ_application_test`** - Verify `succ(zero)` works

### Integration Tests

1. **Church numerals** (`examples/tao/programs/10_church_numerals.core.tao`)
2. **Functions/currying** (`examples/tao/programs/02_functions_and_currying.core.tao`)
3. **Vector dependent** (`examples/tao/programs/13_vector_dependent.core.tao`)

### Expected Results

- **Before**: 526 passed, 7 failures
- **After**: 533+ passed, 0 failures

---

## Risk Analysis

| Risk | Mitigation |
|------|------------|
| Breaking existing tests | Run full test suite after each change |
| Quoting logic complexity | Add detailed comments, test incrementally |
| Performance regression | Profile with step counters |
| Type annotation edge cases | Test with explicit type annotations |

---

## Implementation Order

1. **Add shifted hole substitution functions** (30 min)
2. **Update `quote_domain_with_implicit` with offset** (1 hour)
3. **Update `quote_domain_head` with offset** (15 min)
4. **Update `generalize_holes` to use shifted substitution** (15 min)
5. **Update `infer_app` to use shifted implicit substitution** (30 min)
6. **Run tests and fix regressions** (1-2 hours)
7. **Clean up unused code** (30 min)

**Total**: 3.5-4.5 hours

---

## Success Criteria

- ✅ 533+ tests passing (100%)
- ✅ Church numerals type-check successfully
- ✅ K combinator: `k(10)(20) = 10` works
- ✅ No regressions in existing tests
- ✅ No compiler warnings
- ✅ Clean, maintainable code with comments

---

## Conclusion

Option A (absolute HVar indices) is the cleanest fix because:
1. It addresses the root cause in the quoting logic
2. It makes HVar semantics explicit and unambiguous
3. It requires localized changes to quoting functions
4. It doesn't require complex state threading

The fix is straightforward once the offset tracking is understood.
