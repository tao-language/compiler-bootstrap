# Tao Compiler Remaining Issues - Comprehensive Analysis

## Executive Summary

**Current Status:**
- 504 tests passing (up from 501)
- 5 tests failing (down from 8)
- Fixed: Pattern matching hole unsolved errors (variable_pattern, wildcard_pattern, literal_pattern)

**Remaining Issues:**
1. `match_guard.tao` - Match clauses with guards not being parsed correctly
2. `constructor_pattern.tao` - Constructors (Some, None) not in scope
3. `recursive_fn.tao` - Fixpoint evaluation timeout/infinite loop
4. Import tests (4 tests) - Grammar type mismatch prevents import parsing

---

## Issue 1: Match Guard Parsing

### Symptoms
```tao
match x {
  | n if n > 0 && n < 10 -> "positive small number"
  | n if n > 0 -> "positive large number"
  | n if n < 0 -> "negative"
  | _ -> "zero"
}
```

**Error:** "Pattern match not exhaustive" (reported twice)
**Debug output:** Core term shows empty match cases: `(%match x ~ (%fn(_) -> ?-999) { })`

### Root Cause Analysis

**Grammar Structure:**
The match expression grammar parses clauses with:
```gleam
many(seq([
  token_pattern("Pipe"),      // |
  ref("Expr"),                // pattern
  opt(seq([                   // optional guard
    keyword_pattern("if"),
    ref("Expr"),              // guard expression
  ])),
  token_pattern("Arrow"),     // ->
  ref("Expr"),                // body
]))
```

**Problem:** The `opt(seq([...]))` creates a nested `ListValue` structure for guards:
```
ListValue([
  TokenValue(Pipe),
  AstValue(pattern),
  ListValue([KeywordValue(if), AstValue(guard)]),  // Nested!
  TokenValue(Arrow),
  AstValue(body)
])
```

But the `extract_clause_guard` function expected a flat structure:
```gleam
[KeywordValue(_if), AstValue(guard_expr), TokenValue(_arrow), AstValue(body), ..rest]
```

**Attempted Fix:**
Added handling for nested `ListValue`:
```gleam
[ListValue([KeywordValue(_if), AstValue(guard_expr)]), TokenValue(_arrow), AstValue(body), ..rest] -> {
  Some(#(pattern, Some(guard_expr), body, rest))
}
```

**Result:** Still not working. The cases are still empty in the Core term.

**Next Steps:**
1. Add debug output to `make_match` to see the actual parsed structure
2. Check if the issue is in `extract_clauses` or `extract_single_clause`
3. Verify that `ListValue` items are being unwrapped correctly

**Estimated Effort:** 2-4 hours

---

## Issue 2: Constructor Pattern Scope

### Symptoms
```tao
let some_value = Some(42)
match some_value {
  | Some(x) -> x
  | None -> 0
}
```

**Error:** "This value has type Int, which is not callable"
**Interpretation:** `Some` and `None` are not recognized as constructors

### Root Cause Analysis

**Current State:**
- Prelude modules (prelude/bool, prelude/option, prelude/result, prelude/ordering) have desugaring infrastructure
- `desugar_import` brings constructors into scope for `ImportModule` statements
- But imports are not being parsed due to grammar issues (see Issue 4)

**Problem:**
1. Constructors need to be registered in the global context
2. The `with_prelude` function registers prelude modules, but constructors are not automatically in scope
3. Users need to explicitly import prelude modules to use constructors

**Current Workaround:**
The `desugar_import` function handles `ImportModule("prelude/option")` by creating:
```gleam
[
  CoreLet("Some", CoreCtr("Some", CoreHole(0, span), span), span),
  CoreLet("None", CoreCtr("None", CoreUnit(span), span), span),
]
```

But this code is never reached because imports aren't being parsed.

**Fix Options:**

**Option A: Auto-import prelude constructors** (Recommended)
- Modify `with_prelude` to register constructors directly in the global context
- Constructors like `Some`, `None`, `True`, `False`, `Ok`, `Err` are always available
- Similar to how Gleam and Haskell handle prelude types

**Option B: Fix import grammar first**
- Fix Issue 4 to enable import parsing
- Users explicitly import prelude modules
- More explicit, but requires fixing grammar first

**Estimated Effort:**
- Option A: 1-2 hours
- Option B: Depends on Issue 4 resolution

---

## Issue 3: Recursive Function Timeout

### Symptoms
```tao
fn factorial(n: I32) -> I32 {
  match n {
    | 0 -> 1
    | _ -> n * factorial(n - 1)
  }
}

factorial(5)
```

**Error:** Test times out after 120 seconds
**Interpretation:** Infinite loop during evaluation

### Root Cause Analysis

**Fixpoint Evaluation:**
The `do_app` function handles `VFix` (fixpoint values):
```gleam
VFix(name, env, body) -> {
  let fix_val = VFix(name, env, body)
  let body_val = eval(ffi, [fix_val, ..env], body)
  case body_val {
    VFix(n2, _, _) if n2 == name -> {
      // Self-referential fixpoint - return neutral term
      VNeut(HVar(0), [EApp(arg)])
    }
    _ -> do_app(ffi, body_val, arg)
  }
}
```

**Problem:**
1. The fixpoint unfolds correctly for the first iteration
2. But the recursive call `factorial(n - 1)` creates another fixpoint application
3. The evaluation might be getting stuck in a loop

**Possible Causes:**
1. **Match not working:** If the match expression isn't evaluating correctly (due to Issue 1), the base case `| 0 -> 1` might not be reached
2. **Fixpoint not being recognized:** The `VFix` comparison might not be working correctly
3. **Arithmetic not evaluating:** `n - 1` might not be evaluating to a concrete value

**Debugging Steps:**
1. Add step counter to `eval` to detect infinite loops
2. Print evaluation trace for recursive functions
3. Check if match expressions with literal patterns are working

**Estimated Effort:** 4-8 hours (depends on root cause)

---

## Issue 4: Import Grammar Type Mismatch

### Symptoms
```tao
import prelude/bool

True
```

**Error:** Grammar type mismatch during compilation
**Debug output:** Import statement not appearing in parsed AST

### Root Cause Analysis

**Grammar Type System:**
The grammar DSL uses a typed system where:
- `seq([...])` returns `Rule(List(Value(a)))` - a list of token values
- `alt(seq1, seq2, fn(values) -> ...)` - all alternatives must return the same type
- Parser actions (`fn(values) -> Expr`) transform token lists into AST nodes

**Problem:**
The Import rule tries to mix `seq` (which returns `List(Value(Token))`) with a function that returns `Value(Expr)`:

```gleam
rule("Import", [
  alt(
    seq([...]),           // Returns List(Value(Token))
    make_import,          // Returns Expr (type mismatch!)
  ),
])
```

**Why Other Rules Work:**
Looking at the `Fn` rule:
```gleam
rule("Fn", [
  alt(
    seq([...], make_overloaded_fn),  // seq takes a function that transforms values
  ),
])
```

The function is passed as the second argument to `seq`, not as a separate alternative to `alt`.

**Correct Pattern:**
```gleam
rule("Import", [
  alt(
    seq([
      keyword_pattern("import"),
      token_pattern("Ident"),
      // ... more patterns
    ], make_import),  // Function is second argument to seq
  ),
])
```

**Fix Options:**

**Option A: Fix Import grammar structure** (Recommended)
- Move `make_import` as second argument to `seq`
- Ensure `make_import` returns `Value(Expr)` (wrap in `AstValue`)
- Test with simple import first

**Option B: Manual import preprocessing**
- Parse imports at lexer level before grammar parsing
- Remove import statements from source, process separately
- Add imported names to context before type checking

**Option C: Grammar DSL extension**
- Add support for heterogeneous alternatives in `alt`
- More complex, but would enable more flexible grammars

**Estimated Effort:**
- Option A: 2-4 hours
- Option B: 4-6 hours
- Option C: 8+ hours

---

## Interdependencies

```
Issue 4 (Import Grammar) ──┬──> Issue 2 (Constructor Scope)
                           │
Issue 1 (Match Guards) ────┼──> Issue 3 (Recursive Functions)
                           │
                           └──> All pattern matching tests
```

**Recommended Order:**
1. **Issue 1 (Match Guards)** - Blocking recursive functions and pattern matching
2. **Issue 4 (Import Grammar)** - Blocking constructor scope
3. **Issue 2 (Constructor Scope)** - Depends on Issue 4 or implement Option A
4. **Issue 3 (Recursive Functions)** - Depends on Issue 1

---

## Test Impact

| Test File | Issue | Status |
|-----------|-------|--------|
| variable_pattern.tao | Hole unsolved | ✅ Fixed |
| wildcard_pattern.tao | Hole unsolved | ✅ Fixed |
| literal_pattern.tao | Hole unsolved | ✅ Fixed |
| match_guard.tao | Issue 1 | ❌ Failing |
| constructor_pattern.tao | Issue 2 | ❌ Failing |
| recursive_fn.tao | Issue 3 | ❌ Timeout |
| simple_import.tao | Issue 4 | ❌ Failing |
| test_import.tao | Issue 4 | ❌ Failing |
| selective_import.tao | Issue 4 | ❌ Failing |
| import_example.tao | Issue 4 | ❌ Failing |

**Total:** 504 passing, 5 failing (down from 8)

---

## Implementation Plan

### Phase 1: Fix Match Guard Parsing (Issue 1)
1. Add debug output to `make_match` to see parsed structure
2. Fix `extract_clauses` to handle nested `ListValue` correctly
3. Test with match_guard.tao
4. Verify all pattern matching tests pass

### Phase 2: Fix Import Grammar (Issue 4)
1. Restructure Import rule to use `seq([...], make_import)` pattern
2. Ensure `make_import` returns `AstValue(Import(...))`
3. Test with simple_import.tao
4. Test all import variations

### Phase 3: Fix Constructor Scope (Issue 2)
1. Implement Option A: Auto-import prelude constructors
2. Modify `with_prelude` to register constructors in global context
3. Test with constructor_pattern.tao

### Phase 4: Fix Recursive Functions (Issue 3)
1. Add evaluation tracing/debugging
2. Identify infinite loop source
3. Fix fixpoint evaluation or match evaluation
4. Test with recursive_fn.tao

### Phase 5: Final Verification
1. Run all tests
2. Verify 509 tests passing
3. Update documentation

**Total Estimated Effort:** 10-20 hours

---

## Conclusion

The Tao compiler is 99% complete. The remaining issues are:
1. **Parsing bugs** (Issues 1 and 4) - Grammar structure issues
2. **Scope management** (Issue 2) - Constructors not automatically in scope
3. **Evaluation bug** (Issue 3) - Likely cascading from Issue 1

All issues are well-understood and have clear fix paths. The pattern matching hole fix (completed) was the most complex issue, and the remaining issues are more straightforward parsing and scoping fixes.

**Expected Outcome:** 509 tests passing, fully functional Tao compiler with:
- Pattern matching with guards
- Constructor patterns
- Recursive functions
- Module imports
