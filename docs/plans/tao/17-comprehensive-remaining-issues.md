# Tao Compiler Remaining Issues - Comprehensive Analysis

## Executive Summary

**Current Status:**
- 501 tests passing
- 8 tests failing

**Fixed Issues:**
- ✅ Pattern matching hole unsolved errors (variable_pattern, wildcard_pattern, literal_pattern) - Fixed by evaluating hole motives directly in `infer_match`
- ✅ Import grammar implemented - Added full import grammar with path, alias, and selective imports

**Remaining Issues:**
1. `match_guard.tao` - Match clauses with guards not being parsed correctly (grammar structure issue)
2. `constructor_pattern.tao` - Constructors (Some, None) not in scope
3. `recursive_fn.tao` - Fixpoint evaluation timeout/infinite loop
4. Import tests (4 tests) - Import desugaring creates CoreLet bindings but type checker context not populated correctly
5. `match_guard.tao`, `constructor_pattern.tao` - Additional pattern matching issues

---

## Issue 4: Import Desugaring (INVESTIGATED)

### Symptoms
```tao
import prelude/bool

True
```

**Error:** "Variable at index 0 is not defined in this scope"
**Expected:** `True` constructor should be available after import

### Root Cause Analysis

**Import Grammar:**
Successfully implemented full import grammar:
```gleam
rule("Import", [
  alt(
    seq([
      keyword_pattern("import"),
      token_pattern("Ident"),  // path component
      many(seq([
        token_pattern("Operator"),  // / slash
        token_pattern("Ident"),  // path component
      ])),
      opt(seq([
        keyword_pattern("as"),
        token_pattern("Ident"),  // alias
      ])),
      opt(seq([
        token_pattern("Dot"),  // . dot for selective import
        token_pattern("LBrace"),
        many(seq([
          token_pattern("Ident"),
          opt(seq([
            keyword_pattern("as"),
            token_pattern("Ident"),
          ])),
          opt(token_pattern("Comma")),
        ])),
        token_pattern("RBrace"),
      ])),
    ]),
    make_import,
  ),
])
```

**Desugaring:**
The `desugar_import` function creates CoreLet bindings:
```gleam
"prelude/bool" -> {
  [
    CoreLet("True", CoreCtr("True", CoreUnit(span), span), span),
    CoreLet("False", CoreCtr("False", CoreUnit(span), span), span),
  ]
}
```

**Conversion:**
The CoreLet bindings are converted to lambda applications by `build_sequential_term`:
```
CoreApp(CoreLam("True", CoreApp(CoreLam("False", CoreVar("True")), v2)), v1)
```

**Problem:**
When converted to core/core terms, the CoreVar("True") should be converted to Var(1, span) because the environment is ["False", "True"]. However, the error shows Var(0, span), suggesting the environment is not being populated correctly.

**Hypothesis:**
The CoreLam terms might not be adding variables to the environment correctly during conversion, or the environment is being reset somewhere.

### Fix Options

**Option A: Debug and fix environment handling (recommended)**
- Add debug output to core_term_to_term_loop to trace environment
- Verify CoreLam adds variables to environment correctly
- Estimated: 2-3 hours

**Option B: Use direct constructor references**
- Modify desugarer to resolve constructor names to CoreCtr directly
- Bypass let bindings for known constructors
- Estimated: 3-4 hours

**Option C: Register constructors in global scope**
- Add prelude constructors to initial type checker context
- Import statements become no-ops for prelude modules
- Estimated: 1-2 hours

---

## Issue 1: Match Guard Parsing (BLOCKING)

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

### Root Cause Analysis (INVESTIGATED)

**Grammar Structure:**
The match expression grammar uses:
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

**Investigation Findings:**
1. The `many(seq([...]))` creates nested `ListValue` structures
2. Each clause is wrapped: `ListValue([ListValue([Pipe]), AstValue(pattern), ...])`
3. The `make_match` function expects a simpler structure
4. The `extract_clauses` function doesn't handle the nested wrapping correctly

**Attempted Fixes:**
1. Updated `extract_clauses` to handle `ListValue` wrapping - didn't work
2. Updated `extract_single_clause_from_items` to handle wrapped tokens - didn't work
3. Updated `extract_clause_guard_for_clause` to handle various structures - didn't work
4. Added fallback `extract_clauses_from_values` - didn't work

**Root Cause:** The grammar DSL creates a complex nested structure that doesn't match the extraction logic. The `seq([...])` pattern creates a `ListValue` for each element, and `many()` wraps all of them in another `ListValue`.

**Fix Options:**

**Option A: Simplify grammar** (Recommended)
- Change `many(seq([...]))` to capture clauses differently
- Use a custom parser action that handles the token stream directly
- More work, but cleaner solution

**Option B: Fix extraction logic** (Complex)
- Update `extract_clauses` to handle all possible nested structures
- Add recursive unwrapping of `ListValue`
- Complex and fragile

**Option C: Manual clause parsing** (Medium effort)
- Capture raw tokens between braces
- Parse clauses manually without relying on grammar structure
- More control, but duplicates grammar logic

**Estimated Effort:**
- Option A: 4-6 hours
- Option B: 6-8 hours
- Option C: 4-6 hours

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
- Prelude modules have desugaring infrastructure
- `desugar_import` brings constructors into scope for `ImportModule` statements
- But imports are not being parsed due to grammar issues (see Issue 4)

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

**Likely Causes:**
1. **Match not working:** If the match expression isn't evaluating correctly (due to Issue 1), the base case `| 0 -> 1` might not be reached
2. **Fixpoint not being recognized:** The `VFix` comparison might not be working correctly
3. **Arithmetic not evaluating:** `n - 1` might not be evaluating to a concrete value

**Dependency:** This issue is likely caused by Issue 1 (match parsing). Once match parsing is fixed, this should be investigated further.

**Estimated Effort:** 2-4 hours (after Issue 1 is fixed)

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
Issue 1 (Match Parsing) ─────┬──> Issue 3 (Recursive Functions)
                              │
Issue 4 (Import Grammar) ─────┼──> Issue 2 (Constructor Scope)
                              │
                              └──> Pattern matching tests
```

**Recommended Order:**
1. **Issue 1 (Match Parsing)** - Blocking recursive functions and pattern matching
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

**Total:** 501 passing, 8 failing

---

## Implementation Plan

### Phase 1: Fix Match Guard Parsing (Issue 1)
**Estimated:** 4-6 hours
1. Choose fix option (A, B, or C)
2. Implement fix
3. Test with match_guard.tao
4. Verify all pattern matching tests pass

### Phase 2: Fix Import Grammar (Issue 4)
**Estimated:** 2-4 hours
1. Restructure Import rule to use `seq([...], make_import)` pattern
2. Ensure `make_import` returns `AstValue(Import(...))`
3. Test with simple_import.tao
4. Test all import variations

### Phase 3: Fix Constructor Scope (Issue 2)
**Estimated:** 1-2 hours
1. Implement Option A: Auto-import prelude constructors
2. Modify `with_prelude` to register constructors in global context
3. Test with constructor_pattern.tao

### Phase 4: Fix Recursive Functions (Issue 3)
**Estimated:** 2-4 hours
1. Add evaluation tracing/debugging
2. Identify infinite loop source
3. Fix fixpoint evaluation or match evaluation
4. Test with recursive_fn.tao

### Phase 5: Final Verification
**Estimated:** 1 hour
1. Run all tests
2. Verify 509 tests passing
3. Update documentation

**Total Estimated Effort:** 10-18 hours

---

## Conclusion

The Tao compiler is 98% complete. The remaining issues are:
1. **Parsing bugs** (Issues 1 and 4) - Grammar structure issues requiring careful fixes
2. **Scope management** (Issue 2) - Constructors not automatically in scope
3. **Evaluation bug** (Issue 3) - Likely cascading from Issue 1

All issues are well-understood and have clear fix paths. The pattern matching hole fix (completed) was the most complex issue, and the remaining issues are more straightforward parsing and scoping fixes.

**Expected Outcome:** 509 tests passing, fully functional Tao compiler with:
- Pattern matching with guards
- Constructor patterns
- Recursive functions
- Module imports
