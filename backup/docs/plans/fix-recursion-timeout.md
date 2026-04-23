# Fix for Recursive Function Evaluation Timeout

## Problem Statement

The Tao compiler times out when evaluating recursive functions like `factorial(5)`. The test suite shows 422/425 tests passing, with the 3 failures being:
- `recursive_fn.tao` - factorial function
- `loop.tao` - infinite loop (expected to timeout)
- One other recursion/loop example

**Root Cause**: The `quote` function re-evaluates lambda and fixpoint bodies during reification, causing exponential blowup for recursive functions.

## Analysis

### Current Quote Behavior (BUGGY)

```gleam
VLam(implicit, name, env, body) -> {
  let fresh = VNeut(HVar(lvl), [])
  let body_val = eval(ffi, [fresh, ..env], body)  // ← RE-EVALUATES!
  let body_quote = quote_with_steps(ffi, lvl + 1, body_val, ..., steps - 1)
  Lam(implicit, #(name, Hole(-1, s)), body_quote, s)
}

VFix(name, env, body) -> {
  let fresh = VNeut(HVar(lvl), [])
  let body_val = eval(ffi, [fresh, ..env], body)  // ← RE-EVALUATES!
  let body_quote = quote_with_steps(ffi, lvl + 1, body_val, ..., steps - 1)
  Fix(name, body_quote, s)
}
```

**Problem**: When quoting a closure (VLam) or fixpoint (VFix), we:
1. Create a fresh symbolic variable
2. **Re-evaluate** the body with that variable
3. Quote the result

For recursive functions:
- The closure's environment contains the Fix
- Evaluating the body with a symbolic arg creates stuck terms (Call, Match, etc.)
- Quoting these stuck terms triggers more evaluation
- This creates exponential blowup

### Correct Quote Behavior

Quote should **only reify values to syntax**, not evaluate. The evaluation already happened!

For a closure `VLam("n", env, body)` where the body was already evaluated during `do_app`:
- We should quote the body **as a term**, not re-evaluate it
- The environment is already captured in the closure
- We need to shift De Bruijn indices appropriately

## Solution: Quote Terms Directly

### Key Insight

The `body` in `VLam(implicit, name, env, body)` is already a **Term**, not a Value. We can quote it directly by:
1. Shifting free variables to account for the new binder
2. Recursively quoting sub-terms

### Implementation Plan

#### Step 1: Add Quote-Term Function

Add a new function that quotes a Term (not a Value):

```gleam
/// Quote a term that represents a value in a given environment.
/// 
/// This is used for quoting lambda/fix bodies without re-evaluation.
fn quote_term_in_env(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  // Similar to eval, but quotes instead of evaluating
  // Handles Var by quoting the env value
  // Handles Lam/Fix by recursing with extended env
  // Handles other terms by quoting directly
}
```

#### Step 2: Update VLam Quote Case

```gleam
VLam(implicit, name, env, body) -> {
  // Don't re-evaluate! Quote the body term directly.
  let body_quote = quote_term_in_env(ffi, lvl + 1, body, env, get_span(body), steps - 1)
  Lam(implicit, #(name, Hole(-1, s)), body_quote, s)
}
```

#### Step 3: Update VFix Quote Case

```gleam
VFix(name, env, body) -> {
  // Don't re-evaluate! Quote the body term directly.
  let body_quote = quote_term_in_env(ffi, lvl + 1, body, [VFix(name, env, body), ..env], get_span(body), steps - 1)
  Fix(name, body_quote, s)
}
```

#### Step 4: Implement quote_term_in_env

```gleam
fn quote_term_in_env(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case steps {
    0 -> Hole(-1, s)  // Step limit
    _ -> quote_term_in_env_loop(ffi, lvl, term, env, s, steps)
  }
}

fn quote_term_in_env_loop(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case term {
    Var(i, span) -> {
      // Look up in environment and quote the value
      case list_get(env, i) {
        Some(value) -> quote_with_steps(ffi, lvl, value, span, steps - 1)
        None -> Var(i, span)  // Free variable
      }
    }
    Lam(implicit, param, body, span) -> {
      // Extend environment with the parameter
      // Quote body with shifted level
      let body_quote = quote_term_in_env(ffi, lvl + 1, body, [VNeut(HVar(lvl), []), ..env], span, steps - 1)
      Lam(implicit, param, body_quote, span)
    }
    // For other term types, quote directly (they're already syntax)
    _ -> quote_direct(ffi, lvl, term, s, steps)
  }
}

/// Quote a term directly without environment lookup.
fn quote_direct(
  ffi: FFI,
  lvl: Int,
  term: Term,
  s: Span,
  steps: Int,
) -> Term {
  case term {
    Typ(k, _) -> Typ(k, s)
    Lit(k, _) -> Lit(k, s)
    // ... handle all term constructors
    App(fun, implicit, arg, span) -> {
      let fun_quote = quote_direct(ffi, lvl, fun, span, steps - 1)
      let arg_quote = quote_direct(ffi, lvl, arg, span, steps - 1)
      App(fun_quote, implicit, arg_quote, span)
    }
    // etc.
  }
}
```

### Alternative: Simpler Fix

Actually, there's a simpler approach. The issue is that we're evaluating during quote. We can fix this by:

1. **Not evaluating lambdas during quote** - just quote the body term directly
2. **Not evaluating fixpoints during quote** - just quote the body term directly

But we need to handle the environment correctly. When we encounter a `Var(i)` in the body, we need to look it up in the closure's environment and quote that value.

This is essentially what `quote_term_in_env` does above.

## Implementation Details

### File: `src/core/core.gleam`

#### Add new functions after `quote_elim_with_steps`:

```gleam
/// Quote a term that represents a value in a given environment.
/// 
/// This is used for quoting lambda/fix bodies without re-evaluation.
/// The environment provides the values for free variables in the term.
fn quote_term_in_env(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case steps {
    0 -> Hole(-1, s)
    _ -> quote_term_in_env_loop(ffi, lvl, term, env, s, steps)
  }
}

fn quote_term_in_env_loop(
  ffi: FFI,
  lvl: Int,
  term: Term,
  env: Env,
  s: Span,
  steps: Int,
) -> Term {
  case term {
    Var(i, span) -> {
      // Look up in environment and quote the value
      case list_get(env, i) {
        Some(value) -> quote_with_steps(ffi, lvl, value, span, steps - 1)
        None -> Var(i, span)
      }
    }
    
    Lam(implicit, param, body, span) -> {
      // Extend environment with a fresh neutral for the parameter
      let fresh = VNeut(HVar(lvl), [])
      let body_quote = quote_term_in_env(ffi, lvl + 1, body, [fresh, ..env], span, steps - 1)
      Lam(implicit, param, body_quote, span)
    }
    
    Pi(implicit, name, in_term, out_term, span) -> {
      let in_quote = quote_term_in_env(ffi, lvl, in_term, env, span, steps - 1)
      let fresh = VNeut(HVar(lvl), [])
      let out_quote = quote_term_in_env(ffi, lvl + 1, out_term, [fresh, ..env], span, steps - 1)
      Pi(implicit, name, in_quote, out_quote, span)
    }
    
    Fix(name, body, span) -> {
      // Fix in a term - extend env with the fix itself
      let fix_val = VFix(name, env, body)
      let body_quote = quote_term_in_env(ffi, lvl + 1, body, [fix_val, ..env], span, steps - 1)
      Fix(name, body_quote, span)
    }
    
    App(fun, implicit, arg, span) -> {
      let fun_quote = quote_term_in_env(ffi, lvl, fun, env, span, steps - 1)
      let arg_quote = quote_term_in_env(ffi, lvl, arg, env, span, steps - 1)
      let implicit_quote = list.map(implicit, quote_term_in_env(ffi, lvl, _, env, span, steps - 1))
      App(fun_quote, implicit_quote, arg_quote, span)
    }
    
    Match(arg, motive, cases, span) -> {
      let arg_quote = quote_term_in_env(ffi, lvl, arg, env, span, steps - 1)
      let motive_quote = quote_term_in_env(ffi, lvl, motive, env, span, steps - 1)
      let cases_quote = list.map(cases, fn(c) {
        Case(c.pattern, quote_term_in_env(ffi, lvl, c.body, env, c.body_span, steps - 1), c.guard)
      })
      Match(arg_quote, motive_quote, cases_quote, span)
    }
    
    Call(name, args, span) -> {
      let args_quote = list.map(args, quote_term_in_env(ffi, lvl, _, env, span, steps - 1))
      Call(name, args_quote, span)
    }
    
    // For value-like terms, evaluate and quote
    // (These shouldn't appear in lambda bodies, but handle them)
    Lit(k, span) -> Lit(k, span)
    Typ(k, span) -> Typ(k, span)
    // ... etc for all term constructors
  }
}
```

#### Update `quote_loop` function:

```gleam
fn quote_loop(ffi: FFI, lvl: Int, value: Value, s: Span, steps: Int) -> Term {
  case value {
    // ... other cases unchanged ...
    
    VLam(implicit, name, env, body) -> {
      // Quote the body term directly without re-evaluation
      let body_quote = quote_term_in_env(ffi, lvl + 1, body, env, get_span(body), steps - 1)
      Lam(implicit, #(name, Hole(-1, s)), body_quote, s)
    }
    
    VFix(name, env, body) -> {
      // Quote the body term directly without re-evaluation
      let fix_val = VFix(name, env, body)
      let body_quote = quote_term_in_env(ffi, lvl + 1, body, [fix_val, ..env], get_span(body), steps - 1)
      Fix(name, body_quote, s)
    }
    
    // ... rest unchanged ...
  }
}
```

## Testing

### Unit Tests

Add tests for the new `quote_term_in_env` function:

```gleam
pub fn quote_term_in_env_basic_test() {
  // Test quoting a simple term in an environment
  let env = [VLit(I32(42))]
  let term = Var(0, no_span)
  let result = quote_term_in_env(ffi, 0, term, env, no_span, 1000)
  // Should quote to Lit(42)
  assert(result == Lit(I32(42), no_span))
}

pub fn quote_term_in_env_lambda_test() {
  // Test quoting a lambda without re-evaluation
  let body = Var(0, no_span)  // Just return the parameter
  let lam = Lam([], #("x", Hole(-1, no_span)), body, no_span)
  let val = VLam([], "x", [], body)
  let result = quote(ffi, 0, val, no_span)
  // Should quote to the lambda itself, not evaluate
  assert(result == lam)
}
```

### Integration Tests

The existing `recursive_fn.tao` test should pass after the fix.

## Complexity Analysis

### Before Fix

For `factorial(5)`:
- Evaluation: O(n) steps where n = 5
- Quote: O(2^n) steps due to re-evaluation of symbolic applications
- **Total: O(2^n) - exponential!**

### After Fix

For `factorial(5)`:
- Evaluation: O(n) steps
- Quote: O(n) steps (just traversing the result tree)
- **Total: O(n) - linear!**

## Risks and Mitigations

### Risk 1: Breaking existing functionality

**Mitigation**: Run full test suite after changes. The fix only affects quoting of VLam and VFix, which should produce the same output (just faster).

### Risk 2: Missing environment handling

**Mitigation**: Carefully trace through examples to ensure environment is correctly extended for binders.

### Risk 3: Performance regression for other cases

**Mitigation**: Profile before and after. The new approach should be faster for all cases.

## Success Criteria

- [ ] `recursive_fn.tao` test passes
- [ ] All 425 tests pass
- [ ] No performance regression on other tests
- [ ] Code is well-documented

## Timeline

- **Step 1**: Implement `quote_term_in_env` function (2-3 hours)
- **Step 2**: Update `quote_loop` to use it (1 hour)
- **Step 3**: Add unit tests (1 hour)
- **Step 4**: Run full test suite and debug (2-4 hours)
- **Step 5**: Document and commit (30 min)

**Total: 6-10 hours**
