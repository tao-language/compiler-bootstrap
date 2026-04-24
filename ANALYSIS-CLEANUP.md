# Comprehensive Code Analysis & Cleanup Plan

## Executive Summary

The codebase is in a reasonable "working prototype" state — it compiles, runs, and passes 30 tests. However, there are **14 categories of issues** that need addressing to align with the simplified design plan and maintain good Gleam practices.

The issues fall into three tiers:
- **🔴 Critical** (breaks correctness, violates design plan)
- **🟡 Important** (hurts maintainability, creates tech debt)
- **🟢 Cleanup** (code smell, minor improvements)

---

## 🔴 Critical Issues (Must Fix First)

### 1. Desugarer Panics Instead of Returning Errors

**File:** `src/tao/desugar.gleam` (lines 105, 154, 212, 234)

```gleam
// BAD: Panics on desugaring errors
Error(e) -> panic as e
```

**Problem:** The design plan explicitly states: *"Never use panic for error handling. Return errors properly."* The desugarer should propagate errors through the `Result` type, not crash.

**Fix:** Replace all `panic as e` with `Error(e)`.

---

### 2. De Bruijn Indices Are Not Computed Correctly

**File:** `src/tao/desugar.gleam` (line 32)

```gleam
tao.Var(name, _) -> Ok(#(Var(name: name, index: 0), env))
```

**Problem:** All variables are assigned index `0`, which means every variable resolves to the innermost binder (or causes an error). This is wrong — De Bruijn indices must be computed based on the environment.

**Correct approach:**
```gleam
tao.Var(name, span) -> case env_lookup(env, name) {
  Ok(index) -> Ok(#(Var(name, index), env))
  Error(_) -> Error("Unknown variable: " <> name)
}
```

The same issue affects `desugar_dot` (line 234).

---

### 3. Evaluator Ignores Environment and De Bruijn Levels

**File:** `src/tao/compiler.gleam` (lines 73-84)

```gleam
fn evaluate_term(term: Term) -> Value {
  case term {
    Var(_, _) -> IntVal(0)  // Ignores variable entirely!
    Lam(_, body) -> Closure(param: "x", body: body, env: [])  // Hardcoded param and env
    App(_, _) -> IntVal(0)  // Always returns 0
    // ...
  }
}
```

**Problem:** The evaluator is essentially a dummy that ignores the term structure:
- Variables always return `IntVal(0)` regardless of their index
- Lambdas always use hardcoded param `"x"` and empty env
- Applications always return `IntVal(0)`
- The `state.State(..state)` updates are fieldless (no actual changes)

**Fix:** Either implement proper NBE evaluation (using `core/eval.gleam`), or at minimum pass the term through `core/eval.eval` instead of reimplementing a broken evaluator.

---

### 4. `compiler.gleam` Reimplements `evaluate_term` Instead of Using `core/eval`

**File:** `src/tao/compiler.gleam`

**Problem:** The design plan states: *"Tao passes resolved environments and FFI entries to Core."* The `evaluate_term` function in `compiler.gleam` should delegate to `core/eval.eval`, not reimplement evaluation.

**Fix:**
```gleam
fn compile_expr(expr: Expr, state: State) -> Result(#(Term, Value), List(String)) {
  case desugar.desugar_expr(expr, state.env.bindings) {
    Ok(#(term, new_env)) -> {
      let new_state = state.State(..state, env: state.env, bindings: new_env)
      case core/eval.eval(new_state, term) {
        Ok(value) -> Ok(#(term, value))
        Error(e) -> Error([e])
      }
    }
    Error(e) -> Error([e])
  }
}
```

---

### 5. Type Checker Doesn't Actually Check Types

**File:** `src/core/infer.gleam` (lines 34-41)

```gleam
pub fn check_term(state: State, term: Term, expected: Type) -> Result(State, String) {
  case infer_term(state, term) {
    Ok(st) -> {
      // For prototype, we just return the state after inference
      // In a full implementation, we'd unify inferred type with expected
      Ok(st)  // Always succeeds, ignores expected type!
    }
    Error(e) -> Error(e)
  }
}
```

**Problem:** The `check_term` function is a no-op — it ignores the `expected` parameter and always succeeds. This defeats the purpose of bidirectional type checking.

**Fix:** Either implement proper unification-based checking, or remove `check_term` for the prototype and document it as "not yet implemented".

---

### 6. `unify.gleam` Has No Occurs Check

**File:** `src/core/unify.gleam`

**Problem:** The unification algorithm is missing the occurs check, which can cause infinite loops when unifying recursive types. The design plan explicitly mentions: *"Occurs check prevents infinite recursion during type inference."*

**Fix:** Add an occurs check before substituting variables:
```gleam
fn occurs_check(id: Int, typ: Type) -> Bool {
  case typ {
    TVar(other_id) -> id == other_id
    TPi(_, arg, body) -> occurs_check(id, arg) || occurs_check(id, body)
    TForAll(_, body) -> occurs_check(id, body)
  }
}
```

---

### 7. `state.gleam` Has Redundant Error Type

**File:** `src/core/state.gleam` (lines 30-34)

```gleam
pub type TypeError {
  TypeError(
    message: String,
    span: String,  // Never used - all spans are ""
  )
}
```

**Problem:** The `span` field is never set (all error messages pass `span: ""`). The design plan states: *"Basic error messages with spans are sufficient for a prototype."*

**Fix:** Either:
1. Remove `span` from `TypeError` and use simple strings, or
2. Add `Span` to `TypeError` and propagate it from the desugarer

---

### 8. `eval.gleam` Has Broken `env_to_list`

**File:** `src/core/eval.gleam` (lines 120-124)

```gleam
fn env_to_list(state: state.State) -> List(Value) {
  // This is a simplified version - in practice, we'd need proper De Bruijn level management
  []  // Always returns empty list!
}
```

**Problem:** This function always returns `[]`, which means variable evaluation will always fail. The comment admits this is broken.

**Fix:** Either implement proper De Bruijn level management, or remove this function and use the `core/eval` module's evaluation logic.

---

## 🟡 Important Issues (Hurt Maintainability)

### 9. Duplicate Constructor Names Cause Import Confusion

**Files:** `core/ast.gleam`, `tao/ast.gleam`

**Problem:** Both `core/ast` and `tao/ast` define `Var`, `Lit`, `Hole`, `Match` constructors with different fields. This causes confusion when importing:

```gleam
import core/ast.{Var, Lam, App}
import tao/ast.{Var, Lambda, Call}  // Different Var!
```

**Fix:** Use explicit aliases in imports:
```gleam
import core/ast.{type Term, Var, Lam, App}
import tao/ast.{type Expr, Var as ExprVar, Lambda, Call}
```

---

### 10. Unused Imports and Types

**Files:** Multiple files

**Problem:** Many files import types that are never used. Examples:

```gleam
// src/core/state.gleam
import core/ast.{type Type, type Term, type Value}  // Term and Value unused

// src/tao/compiler.gleam
import gleam/list  // Never used
import core/ast.{type Type}  // Never used
```

**Fix:** Remove all unused imports. Gleam will complain at compile time, so just fix what breaks.

---

### 11. Fieldless Record Updates

**Files:** Multiple files

**Problem:** Many record updates don't actually change any fields:

```gleam
let new_state = state.State(
  env: state.State(..state).env,
  errors: state.State(..state).errors,
  hole_bindings: state.State(..state).hole_bindings,
)
// This is equivalent to: let new_state = state
```

**Fix:** Either remove the fieldless update, or actually update the fields that need changing.

---

### 12. Missing `Span` in Core Types

**File:** `src/core/ast.gleam`

**Problem:** Core types (`Term`, `Value`, `Type`) don't include `Span` for error reporting. The design plan shows:

```gleam
pub type Term {
  Var(index: Int, span: Span)
  Lam(param: String, body: Term, span: Span)
  // ...
}
```

**Fix:** Add `Span` to all `Term` and `Type` constructors. This is essential for error messages.

---

### 13. `infer.gleam` Imports Unused Modules

**File:** `src/core/infer.gleam`

```gleam
import core/unify  // Never used!
```

**Problem:** The `unify` module is imported but never called. This creates a dependency that doesn't exist.

**Fix:** Remove the import, or implement unification-based type checking.

---

### 14. `desugar_match` Returns Placeholder

**File:** `src/tao/desugar.gleam` (lines 154-160)

```gleam
fn desugar_match(arg: tao.Expr, cases: List(tao.MatchClause), env: List(#(String, Type))) -> Result(#(Term, List(#(String, Type))), String) {
  case desugar_expr(arg, env) {
    Ok(#(arg_term, new_env)) -> {
      // Simplified: just return a placeholder match case
      Ok(#(Match(scrutinee: arg_term, cases: [Case(pattern: PatVar(name: "_"), body: Lit(LInt(0)))]), new_env))
    }
    Error(e) -> Error(e)
  }
}
```

**Problem:** Match expressions are desugared to a dummy pattern matching on `_` and returning `0`. This is completely non-functional.

**Fix:** Either implement proper match desugaring, or return `Error("Match not implemented")`.

---

## 🟢 Cleanup (Code Smell & Minor Improvements)

### 15. Naming Inconsistencies

**Files:** Multiple files

**Problem:** Inconsistent naming conventions:
- `desugar_lambda` vs `desugar_call` vs `desugar_match` (inconsistent)
- `Term` fields use named parameters: `Lam(param: String, body: Term)` vs `Var(name: String, index: Int)`
- Some files use `type X` syntax, others don't

**Fix:** Standardize on one convention. Gleam recommends:
- All constructor fields use named parameters
- All functions use consistent naming: `verb_noun` format

---

### 16. Commented-Out/Incomplete Code

**Files:** `src/core/eval.gleam`, `src/core/infer.gleam`

**Problem:** Comments like:
```gleam
// For prototype, we just return the state after inference
// In a full implementation, we'd unify inferred type with expected
```

**Fix:** Either implement the full behavior, or remove the comment and leave a TODO with a link to the design document.

---

### 17. `exhaustiveness.gleam` Is a No-Op

**File:** `src/core/exhaustiveness.gleam`

**Problem:** The `check_patterns` function always returns `True` if there's at least one case. This is completely non-functional.

**Fix:** Either implement proper Maranget-style exhaustiveness checking, or remove the function and document it as "not yet implemented."

---

### 18. `quote.gleam` Has Hardcoded Error Message

**File:** `src/core/quote.gleam` (line 19)

```gleam
ErrVal -> Err(message: "quote error")
```

**Problem:** Hardcoded error message doesn't provide useful debugging information.

**Fix:** Use a more descriptive message or pass context from the caller.

---

### 19. `grammar.gleam` Has `panic` in Parser

**File:** `src/syntax/grammar.gleam` (line 111)

```gleam
State(values: values, errors: errs, ..) -> ParseResult(ast: panic, errors: errs)
```

**Problem:** The parser panics on certain parse states instead of returning an error.

**Fix:** Return a `ParseError` instead of using `panic`.

---

### 20. Test Coverage Is Minimal

**File:** `test/compiler_bootstrap_test.gleam`

**Problem:** Only 30 tests exist, and they mostly test the lexer. The design plan calls for ~235 tests:

| Category | Current | Target |
|----------|---------|--------|
| Lexer | 3 | 15 |
| Parser | 0 | 30 |
| Core type checker | 0 | 50 |
| Core evaluator | 0 | 25 |
| Quote | 0 | 15 |
| Unification | 0 | 20 |
| Exhaustiveness | 0 | 20 |
| Desugarer | 0 | 40 |
| Tao parser | 0 | 20 |
| Compiler | 0 | 20 |

**Fix:** Prioritize tests for the critical path: desugarer → type checker → evaluator → compiler.

---

## Recommended Action Plan

### Phase 1: Fix Core Correctness (1-2 days)
1. Fix De Bruijn index computation in `desugar.gleam`
2. Fix `evaluate_term` to use `core/eval.eval` or implement proper NBE
3. Remove all `panic` calls, replace with proper error propagation
4. Fix `env_to_list` or remove it

### Phase 2: Align with Design Plan (1-2 days)
5. Add `Span` to all `Term` and `Type` constructors
6. Fix `unify.gleam` to include occurs check
7. Implement proper `check_term` or remove it
8. Remove unused imports and types

### Phase 3: Improve Maintainability (1 day)
9. Standardize naming conventions
10. Add `Span` to error types
11. Remove fieldless record updates
12. Fix `exhaustiveness.gleam` or mark as TODO

### Phase 4: Add Tests (2-3 days)
13. Add desugarer tests (priority: variable resolution)
14. Add type checker tests (priority: Pi types, application)
15. Add evaluator tests (priority: lambda, application)
16. Add compiler integration tests

---

## Alignment with Design Plan

| Design Principle | Current State | Action Needed |
|-----------------|---------------|---------------|
| **"Build the smallest thing that works"** | ✅ Mostly followed | Fix critical bugs first |
| **No visitor pattern** | ✅ Followed | N/A |
| **No error codes** | ✅ Followed | N/A |
| **Error accumulation** | ⚠️ Partially followed | Fix error propagation in desugarer |
| **NBE-based type checking** | ❌ Not implemented | Implement unification-based checking |
| **No CoreTerm duplication** | ✅ Followed | N/A |
| **Generic literals** | ✅ Followed | N/A |
| **Explicit immutability** | ⚠️ Followed but broken | Fix De Bruijn indices |

---

## Files That Need the Most Attention

1. **`src/tao/desugar.gleam`** — Panics, broken De Bruijn, incomplete match
2. **`src/tao/compiler.gleam`** — Dummy evaluator, fieldless updates
3. **`src/core/infer.gleam`** — No-op `check_term`, unused imports
4. **`src/core/eval.gleam`** — Broken `env_to_list`, unused functions
5. **`src/core/unify.gleam`** — Missing occurs check
6. **`src/core/state.gleam`** — Redundant error type
7. **`src/core/ast.gleam`** — Missing `Span` in types

---

## Expected Outcomes

After completing this cleanup:
- ✅ All code compiles without warnings
- ✅ No `panic` calls in the codebase
- ✅ De Bruijn indices computed correctly
- ✅ Type checker actually checks types
- ✅ Evaluator properly normalizes terms
- ✅ Error messages include source spans
- ✅ Test coverage reaches ~100 tests (minimum viable)
- ✅ Code follows Gleam naming conventions
- ✅ Aligns with `plans/rewrite/14-simplified-design.md`
