# Evaluation Timeout Analysis

## Problem Summary

The Tao compiler cannot evaluate `factorial(5)` - it times out during the quote phase with 422/425 tests passing. This is a critical failure for a programming language.

## Current Architecture

### Evaluation Model

1. **Terms** are evaluated to **Values** using `eval(ffi, env, term)`
2. **Values** are quoted back to **Terms** (normal form) using `quote(ffi, lvl, value, span)`
3. Both functions now have step counters (1,000,000 default) to prevent infinite loops

### Factorial Desugaring

```tao
fn factorial(n: I32) -> I32 {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}
factorial(5)
```

Desugars to core:
```
App(
  Fix("factorial", 
    Lam("n", 
      Match(Var(0), 
        Unit,  -- motive
        [
          Case(Pattern(Lit(0)), Lit(1)),
          Case(Pattern(Any), Call("mul", [Var(0), App(Fix(...), Call("sub", [Var(0), Lit(1)]))]))
        ]
      )
    )
  ),
  Lit(5)
)
```

## Expected Evaluation Trace

```
factorial(5)
→ match 5 { | 0 → 1 | _ → 5 * factorial(4) }
→ 5 * factorial(4)
→ 5 * match 4 { | 0 → 1 | _ → 4 * factorial(3) }
→ 5 * (4 * factorial(3))
→ 5 * (4 * (3 * factorial(2)))
→ 5 * (4 * (3 * (2 * factorial(1))))
→ 5 * (4 * (3 * (2 * (1 * factorial(0)))))
→ 5 * (4 * (3 * (2 * (1 * 1))))
→ 5 * (4 * (3 * (2 * 1)))
→ 5 * (4 * (3 * 2))
→ 5 * (4 * 6)
→ 5 * 24
→ 120
```

## Root Cause Analysis

### Issue 1: Step Counter Decrement Strategy

**Current behavior**: Steps are decremented by 1 for EACH recursive call to `eval_loop` and `quote_with_steps`.

**Problem**: For a computation tree with N nodes, we need N steps. But the step counter is shared across ALL recursive calls, including:
- Evaluating function and argument in App
- Unfolding Fix
- Evaluating match branches
- Evaluating Call arguments
- Quoting each sub-term

**Calculation for factorial(5)**:
- 5 recursive calls
- Each call: ~20 eval steps + ~20 quote steps
- Total: ~200 steps minimum

With 1,000,000 steps, this should work. But something is wrong.

### Issue 2: Quote Phase Re-evaluation

**Critical Bug**: In `quote_loop`, when quoting a `VLam`:

```gleam
VLam(implicit, name, env, body) -> {
  let fresh = VNeut(HVar(lvl), [])
  let body_val = eval(ffi, [fresh, ..env], body)  -- RE-EVALUATES!
  let body_quote = quote_with_steps(ffi, lvl + 1, body_val, ..., steps - 1)
  ...
}
```

**Problem**: Quoting a lambda RE-EVALUATES the body with a fresh variable. For recursive functions, this can trigger unbounded computation!

For factorial:
1. After evaluation, we have a closure: `VLam("n", env, body)` where env contains the Fix
2. When quoting, we eval the body with a symbolic argument
3. The match can't reduce (symbolic arg ≠ 0)
4. But the `_` branch creates: `Call("mul", [symbolic, App(fix, sub(symbolic, 1))])`
5. This is a NEUTRAL term that gets quoted as-is
6. But quoting the Call quotes each arg...
7. And `App(fix, ...)` might trigger more evaluation!

### Issue 3: VFix Quoting

```gleam
VFix(name, env, body) -> {
  let fresh = VNeut(HVar(lvl), [])
  let body_val = eval(ffi, [fresh, ..env], body)  -- RE-EVALUATES!
  let body_quote = quote_with_steps(ffi, lvl + 1, body_val, ..., steps - 1)
  Fix(name, body_quote, s)
}
```

Same issue - quoting a fixpoint re-evaluates the body!

### Issue 4: Neutral Term Spine Explosion

When evaluation times out, it returns `VNeut(HStepLimit, [])`. But if evaluation partially completes, we might get:

```
VNeut(HVar(0), [EApp(Lit(5)), EApp(Lit(4)), EApp(Lit(3)), ...])
```

A long spine of applications. When quoting:
- `quote_neut_with_steps` folds over the spine
- Each `EApp(arg)` calls `quote_with_steps(ffi, lvl, arg, s, steps - 1)`
- But `steps` is the SAME for all spine elements (not decremented between them!)
- So a spine of length N only consumes 1 step total!

This is actually OK for step counting, but the quote of each arg still costs steps.

## Evidence from Stack Traces

```
QuoteLoop, 5, [File("src/core/core.gleam"), Line(1218)]
MapLoop, 3, [File("src/gleam/list.gleam"), Line(391)]
QuoteLoop, 5, ...
MapLoop, 3, ...
```

The alternating pattern shows:
- `quote_loop` (arity 5: ffi, lvl, value, s, steps)
- `list.map` (arity 3: list, fn, acc)

This happens when quoting:
- `VRcd(fields)` - maps over fields
- `VCall(name, args)` - maps over args
- `VRecord(fields)` - maps over fields

For factorial, we shouldn't have any of these in the final result (should be `VLit(120)`).

**Conclusion**: Evaluation is NOT completing successfully. The result is a stuck term (VCall or VNeut), not VLit(120).

## Hypothesis

**Primary Hypothesis**: The built-in `mul` function is not being applied during evaluation, creating a growing tree of `VCall("mul", ...)` terms.

**Possible causes**:
1. FFI lookup failing (name mismatch?)
2. Arguments not concrete when expected
3. Step limit exceeded during evaluation (not quote)
4. Match not reducing properly

## Investigation Steps

1. **Add debug output** to see what value is produced before quoting
2. **Check FFI names** - does Tao's `mul` match core's `"mul"`?
3. **Test simpler cases** - does `2 * 3` work?
4. **Check match reduction** - does `match 5 { | 0 → 1 | _ → 5 }` work?

## Solution Options

### Option 1: Increase Step Limit (Band-aid)

```gleam
pub fn eval(ffi, env, term) { eval_with_steps(ffi, env, term, 10_000_000) }
pub fn quote(ffi, lvl, value, s) { quote_with_steps(ffi, lvl, value, s, 10_000_000) }
```

**Pros**: Simple, might work for small examples
**Cons**: Doesn't fix root cause, will fail on larger programs

### Option 2: Fix Step Counting

Current: Decrement by 1 per recursive call
Better: Decrement by estimated cost of operation

```gleam
// Cost model:
const EVAL_APP_COST = 5
const EVAL_MATCH_COST = 10
const EVAL_CALL_COST = 3
const QUOTE_LAM_COST = 20  // Includes re-evaluation!
```

**Pros**: More accurate
**Cons**: Complex, still doesn't fix re-evaluation issue

### Option 3: Don't Re-evaluate During Quote

**Key insight**: Quote should NOT evaluate. It should only reify values to syntax.

For `VLam`, instead of:
```gleam
let fresh = VNeut(HVar(lvl), [])
let body_val = eval(ffi, [fresh, ..env], body)
quote(ffi, lvl + 1, body_val, ...)
```

We should:
```gleam
// Don't eval - just quote the term directly with shifted env
quote_term_with_env(ffi, lvl + 1, body, env, ...)
```

**Pros**: Eliminates re-evaluation, faster, more predictable
**Cons**: Requires significant refactoring

### Option 4: Memoization/Caching

Cache results of evaluation and quoting to avoid redundant work.

**Pros**: Could dramatically improve performance
**Cons**: Complex, needs cache invalidation

### Option 5: Separate Evaluation from Normalization

Don't normalize by default. Only normalize when needed (e.g., for display).

**Pros**: Faster for most operations
**Cons**: Changes semantics, might break other code

### Option 6: Fix the Real Bug (Recommended)

Based on the stack trace evidence, the issue is likely:
1. Builtins not being applied (check FFI names)
2. Match not reducing (check pattern matching)
3. Step limit too low for evaluation (not quote)

**Investigation needed first!**

## Immediate Action Plan

1. **Add debug test** to print the value before quoting:
   ```gleam
   let value = eval(initial_state.ffi, [], term)
   io.println("DEBUG: value = " <> inspect(value))
   ```

2. **Test builtin application**:
   ```tao
   add(2, 3)  -- Should be 5
   mul(4, 5)  -- Should be 20
   ```

3. **Test match reduction**:
   ```tao
   match 5 {
     | 0 -> 1
     | _ -> 42
   }  -- Should be 42
   ```

4. **Check FFI registry** - verify names match between Tao desugaring and core FFI

5. **If builtins work**, the issue is in recursive evaluation - need Option 3 (don't re-evaluate during quote)

## Long-term Architecture Recommendations

1. **Separate evaluation from normalization** - don't normalize by default
2. **Add proper cost model** - track computational complexity
3. **Add memoization** - cache evaluation results
4. **Add better error messages** - "evaluation timed out" vs silent wrong output
5. **Consider lazy evaluation** - only evaluate what's needed
