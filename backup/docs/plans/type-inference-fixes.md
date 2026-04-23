# Type Inference and Type Checking Fixes - Comprehensive Plan

## Executive Summary

This document provides a detailed implementation plan to fix the remaining test failures in the compiler-bootstrap project. 

**Current Status:** 421 passed, 4 failures (as of 2026-03-20)
**Target:** 519+ passed, 0 failures

---

## Completed Fixes ✅

### Phase 1: Quick Wins (DONE)
1. ✅ **List constructors** - Added `Cons` and `Nil` to prelude
2. ✅ **Test/Run desugaring** - Implemented full support for test and run statements

### Phase 2: Type Inference (DONE)
3. ✅ **Fix type inference** - Implemented assume-and-verify approach for recursive functions

**Results:** Fixed `test_example.tao`, `simple_for.tao`, `for_loop.tao`, `while_loop.tao`, `loop.tao`, `recursive_fn.tao`

---

## Remaining Failures Analysis

| # | Test | Category | Root Cause | Priority | Est. Effort |
|---|------|----------|------------|----------|-------------|
| 1 | `match_guard.tao` | Exhaustiveness | Guard conditions not considered | P1 | 4-6 hours |
| 2 | Recursion tests | Runtime | Infinite loop during normalization | P1 | 3-4 hours |

---

## Phase 3: Advanced Fixes (P1)

### 3.1 Fix Exhaustiveness Checking with Guards

**Affected Test:** `match_guard.tao`

**Problem:** The exhaustiveness checker (Maranget's algorithm) treats patterns with guards as if they have no guards, leading to false positives for redundant patterns.

**Example:**
```tao
match x {
  | n if n > 0 && n < 10 -> 1  // Handles (0, 10)
  | n if n > 0 -> 2            // Should handle [10, ∞), but flagged as redundant
  | n if n < 0 -> 3            // Handles (-∞, 0)
  | _ -> 0                     // Handles 0
}
```

**Root Cause:** The `is_pattern_covered_by` function in `src/core/core.gleam` only compares pattern structure, not guard conditions.

**Current Implementation (line ~3084):**
```gleam
fn is_pattern_covered_by(s: State, pattern1: Pattern, pattern2: Pattern) -> Bool {
  // Only checks if pattern2's constructor covers pattern1's constructor
  // Does NOT consider guard conditions
}
```

**Solution Options:**

#### Option A: Conservative Skip (Recommended for MVP)
When a pattern has a guard, skip exhaustiveness checking for that pattern and all subsequent patterns.

**Pros:**
- Simple implementation
- No false positives
- Safe (may miss some real redundancies, but won't report false ones)

**Cons:**
- Less precise exhaustiveness checking when guards are present

**Implementation:**
```gleam
fn check_exhaustiveness(clauses: List(Clause), ty: Type) -> List(Error) {
  list.fold(clauses, [], fn(acc, clause) {
    case clause.guard {
      Some(_) -> {
        // Guard present - skip exhaustiveness for this and remaining clauses
        // Add warning that exhaustiveness is not checked with guards
        acc
      }
      None -> {
        // No guard - check normally
        check_clause_coverage(clause, acc, ty)
      }
    }
  })
}
```

#### Option B: Guard-Aware Checking (Full Solution)
Extend Maranget's algorithm to track guard conditions and reason about their logical relationships.

**Pros:**
- Precise exhaustiveness checking
- Can detect real redundancies even with guards

**Cons:**
- Complex implementation
- Requires SMT solver or constraint reasoning
- May be slow for complex guards

**Implementation Approach:**
1. Represent guards as logical formulas
2. Use constraint solving to check if guard1 ∨ guard2 ∨ ... covers all cases
3. For simple comparisons (>, <, ==), use interval arithmetic

---

### 3.2 Handle Infinite Loops in Evaluation

**Affected Tests:** Recursion tests that timeout during normalization

**Problem:** The `do_app` function's fixpoint unfolding can cause infinite recursion for certain recursive functions during normalization/evaluation.

**Current Implementation (line ~926):**
```gleam
fn do_app(ffi: FFI, fun: Value, arg: Value) -> Value {
  case fun {
    VFix(name, env, body) -> {
      let fix_val = VFix(name, env, body)
      let body_val = eval(ffi, [fix_val, ..env], body)
      // Only checks if body evaluates to same fixpoint
      case body_val {
        VFix(n2, _, _) if n2 == name -> VNeut(HVar(0), [EApp(arg)])
        _ -> do_app(ffi, body_val, arg)  // Can still loop infinitely
      }
    }
    ...
  }
}
```

**Root Cause:** The self-reference check only catches the case where `body_val` is the same fixpoint. It doesn't catch:
1. Indirect recursion (A calls B calls A)
2. Deep recursion that eventually loops
3. Normalization of recursive types

**Solution Options:**

#### Option A: Step Counter (Recommended)
Add a step counter to the evaluation that returns a neutral term after N steps.

**Pros:**
- Simple implementation
- Guaranteed termination
- Configurable limit

**Cons:**
- May stop legitimate long computations
- Need to choose appropriate limit

**Implementation:**
```gleam
pub type EvalState {
  EvalState(
    ffi: FFI,
    env: Env,
    steps: Int,
    max_steps: Int,
  )
}

pub fn eval_with_limit(ffi: FFI, env: Env, term: Term, max_steps: Int) -> Value {
  let state = EvalState(ffi: ffi, env: env, steps: 0, max_steps: max_steps)
  eval_loop(state, term)
}

fn eval_loop(state: EvalState, term: Term) -> Value {
  case state.steps >= state.max_steps {
    True -> VNeut(HStepLimit, [])  // Return neutral term
    False -> {
      let new_state = EvalState(..state, steps: state.steps + 1)
      // ... evaluate normally with new_state
    }
  }
}
```

#### Option B: Fuel-Based Evaluation
Pass "fuel" that decreases with each evaluation step.

**Pros:**
- Similar to step counter
- More composable

**Cons:**
- Same limitations as step counter

#### Option C: Lazy Normalization
Only normalize when necessary for type checking.

**Pros:**
- Avoids unnecessary computation
- More efficient

**Cons:**
- Complex implementation
- May delay errors

---

## Implementation Plan

### Step 1: Fix Exhaustiveness with Guards (Conservative Approach)
**File:** `src/core/core.gleam`
**Function:** `infer_match` and related exhaustiveness checking

1. Add guard detection to clause processing
2. Skip exhaustiveness checking when guards are present
3. Optionally add a warning that exhaustiveness is not checked

**Estimated time:** 2-3 hours

### Step 2: Add Step Counter to Evaluation
**File:** `src/core/core.gleam`
**Functions:** `eval`, `do_app`, `do_match`, etc.

1. Add `EvalConfig` with `max_steps` field
2. Thread step counter through all evaluation functions
3. Return neutral term when limit exceeded
4. Update `normalize` to use step-limited evaluation

**Estimated time:** 3-4 hours

### Step 3: Test and Verify
1. Run full test suite
2. Verify no new failures
3. Check that previously failing tests now pass

**Estimated time:** 1 hour

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Step counter too low | Medium | False errors | Make configurable, start with 10000 |
| Step counter too high | Low | Slow tests | Profile and adjust |
| Guard checking too conservative | Medium | Miss real errors | Add warning messages |
| Performance regression | Low | Slow type checking | Benchmark before/after |

---

## Success Criteria

- [ ] `match_guard.tao` type checks without errors
- [ ] All recursion tests complete without timeout
- [ ] No new test failures introduced
- [ ] Total tests: 519+ passing
  // ... existing constructors ...
  
  // List type: data List(a) = Cons(a, List(a)) | Nil
  // List : Type(0) -> Type(0), represented as Typ(1)
  #("Cons", CtrDef(["a"], Rcd([#("head", Var(0, no_span)), #("tail", App(Var(0, no_span), [], Var(0, no_span))]), Typ(0, no_span))),
  #("Nil", CtrDef(["a"], Unit(no_span), Typ(0, no_span))),
]
```

**Note:** The actual constructor definition needs to match the existing pattern. Looking at the current prelude:

```gleam
#("Some", CtrDef(["a"], Var(0, no_span), Typ(0, no_span))),
```

For List, we need:
- `Cons` takes a pair (head, tail) where head : a and tail : List(a)
- `Nil` is nullary (takes Unit)

**Simplified approach** (matching existing pattern):

```gleam
// Cons : (a : Type(0)) -> (a * List(a)) -> List(a)
// For now, use a simpler representation
#("Cons", CtrDef(["a"], Rcd([#("head", Var(0, no_span)), #("tail", Hole(0, no_span))]), Typ(0, no_span))),
#("Nil", CtrDef(["a"], Unit(no_span), Typ(0, no_span))),
```

#### File: `src/tao/global_context.gleam`

Update `with_prelude` to include List in public_names:

```gleam
let list_ref = ModuleRef(
  path: "prelude/list",
  public_names: ["List", "Cons", "Nil", "head", "tail", "is_empty", "length", "map", "fold"],
  value: None,
  source: None,
)

// Insert list module
GlobalContext(
  ..ctx4,  // after ordering
  modules: dict.insert(ctx4.modules, "prelude/list", list_ref),
)
```

**Testing:**
```bash
gleam run check examples/tao/programs/05-control-flow/simple_for.tao
# Should pass type checking (may still have runtime issues)
```

---

### 1.2 Implement Test/Run Statement Desugaring

**Affected Tests:** `test_example.tao`

**Problem:** Test and Run statements are parsed but not properly desugared. The test framework evaluates test bodies but doesn't separate test evaluation from the final `run` expression.

**Current Behavior:**
- `test "name" { expr }` → evaluates to `expr` (contributes to module result)
- `run expr` → evaluates to `expr` (should be the ONLY module result)
- Module returns last test result (12) instead of `run` result (42)

**Required Changes:**

#### File: `src/tao/ast.gleam`

Add Test and Run constructors to Expr type (around line 50):

```gleam
pub type Expr {
  // ... existing constructors ...
  
  /// Test statement: test "name" { body }
  /// Tests are evaluated for side effects but don't contribute to module result
  Test(name: String, body: Expr, span: Span)
  
  /// Run statement: run expr
  /// The run expression determines the module's output
  Run(value: Expr, span: Span)
}
```

#### File: `src/tao/desugar.gleam`

Add desugaring for Test and Run expressions (around line 1035, in `desugar_expr_core`):

```gleam
pub fn desugar_expr_core(
  expr: Expr,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  case expr {
    // ... existing cases ...
    
    ast.Test(_name, body, _span) -> {
      // Tests evaluate the body but return Unit
      // The test harness (separate from compiler) handles reporting
      let #(core_body, dc1) = desugar_expr_core(body, dc)
      // Return Unit to indicate test completed (test harness checks for errors)
      #(CoreDoBlock([core_body], CoreUnit(_span), _span), dc1)
    }
    
    ast.Run(value, span) -> {
      // Run evaluates and returns the value as the module result
      desugar_expr_core(value, dc)
    }
    
    // ... rest of cases ...
  }
}
```

#### File: `src/tao/desugar.gleam`

Update `desugar_stmt` to handle Test and Run as statements (around line 361):

```gleam
pub fn desugar_stmt(
  stmt: Stmt,
  dc: DesugarContext,
) -> #(List(CoreTerm), DesugarContext) {
  case stmt {
    // ... existing cases ...
    
    StmtTest(name, body, span) -> {
      // Test statement: evaluate body, don't add to scope
      let #(core_body, dc1) = desugar_expr_core(body, dc)
      // Create a test term that evaluates the body
      let test_term = CoreDoBlock([core_body], CoreUnit(span), span)
      #([test_term], dc1)
    }
    
    StmtRun(value, span) -> {
      // Run statement: evaluate and return as module result
      // This is handled specially in desugar_module
      let #(core_value, dc1) = desugar_expr_core(value, dc)
      #([core_value], dc1)
    }
    
    // ... rest of cases ...
  }
}
```

#### File: `src/tao/desugar.gleam`

Update `desugar_module` to handle Run as the final expression (around line 194):

```gleam
pub fn desugar_module(
  module: Module,
  ctx: GlobalContext,
) -> #(Term, DesugarContext) {
  let dc = DesugarContext(
    global: ctx,
    current_module: module.path,
    local_scope: [],
    loop_stack: [],
  )

  // Check if the last statement is a Run statement
  case get_last_stmt(module.body) {
    StmtRun(value, _span) -> {
      // Run statement: desugar all statements, but use run value as result
      let all_but_last = drop_last(module.body)
      let #(core_stmts, dc1) = desugar_stmts(all_but_last, dc)
      let #(core_result, _dc2) = desugar_expr_core(value, dc1)
      let core_term = CoreDoBlock(core_stmts, core_result, module.span)
      let term = core_term_to_term(core_term)
      #(term, dc1)
    }
    _ -> {
      // Existing logic for expression-style and declaration-style modules
      // ...
    }
  }
}
```

**Testing:**
```bash
gleam run run examples/tao/programs/03-test-run/test_example.tao
# Should output: 42
```

---

## Phase 2: Type Inference Fixes (P1)

### 2.1 Fix Fixpoint Type Inference

**Affected Tests:** `recursive_fn.tao`, `while_loop.tao`, `for_loop.tao`

**Problem:** The type checker cannot infer types for recursive functions and loops using the `fix` operator. The error `%pi<_0>(n: var[0]) -> ... and Int are incompatible types` indicates the fixpoint's type is not being properly unified with the expected type.

**Current Behavior:**
```gleam
// In infer function (src/core/core.gleam)
// No case for Fix term - falls through to error
```

**Required Changes:**

#### File: `src/core/core.gleam`

Add Fix type inference in the `infer` function (around line 2050):

```gleam
pub fn infer(s: State, term: Term) -> #(Value, Type, State) {
  case term {
    // ... existing cases ...
    
    Fix(name, body, span) => {
      // Fixpoint type inference using the "assume and verify" approach:
      // 1. Create a hole for the fixpoint's type
      // 2. Add the fixpoint to the context with this type
      // 3. Infer the body type
      // 4. Unify the body type with the assumed type
      
      let env = get_env(s)
      let holes_before = s.hole
      
      // Step 1: Create a hole for the fixpoint type
      let #(fix_ty_hole, s) = new_hole(s)
      let fix_hole_id = s.hole - 1
      
      // Step 2: Add fixpoint to context
      let #(_var, s) = def_var(s, name, fix_ty_hole)
      
      // Step 3: Infer body type (body can reference the fixpoint)
      let #(body_val, body_ty, s) = infer(s, body)
      
      // Step 4: Unify body type with fixpoint type
      case unify(s, body_ty, fix_ty_hole, span, span) {
        Ok(s_unified) => {
          // Force the unified type to get the solved type
          let solved_ty = force(s_unified.ffi, s_unified.sub, fix_ty_hole)
          
          // Quote the body value
          let body_quoted = quote(s_unified.ffi, list.length(env), body_val, span)
          
          // Return fixpoint value and solved type
          #(VFix(name, env, body_quoted), solved_ty, s_unified)
        }
        Error(e) => {
          // Unification failed - record error and return error type
          #(VErr, VErr, with_err(s, e))
        }
      }
    }
    
    // ... rest of cases ...
  }
}
```

**Key Insight:** The fixpoint type is inferred by:
1. Assuming the fixpoint has some type `?A`
2. Checking that the body has type `?A` under this assumption
3. Unifying `?A` with the body type solves the hole

This is the standard approach for recursive type inference.

**Testing:**
```bash
gleam run check examples/tao/programs/04-recursion/recursive_fn.tao
gleam run check examples/tao/programs/05-control-flow/while_loop.tao
gleam run check examples/tao/programs/05-control-flow/for_loop.tao
```

---

## Phase 3: Advanced Fixes (P2)

### 3.1 Fix Exhaustiveness Checking with Guards

**Affected Tests:** `match_guard.tao`

**Problem:** The exhaustiveness checker (Maranget's algorithm) incorrectly flags guarded patterns as redundant. The algorithm doesn't account for guard conditions when determining pattern coverage.

**Example:**
```tao
match x {
  | n if n > 0 && n < 10 -> 1  // Pattern 1
  | n if n > 0 -> 2            // Pattern 2 - incorrectly flagged as redundant
  | n if n < 0 -> 3            // Pattern 3 - incorrectly flagged as redundant
  | _ -> 0                     // Pattern 4
}
```

**Why patterns are NOT redundant:**
- Pattern 1 covers: `0 < n < 10`
- Pattern 2 covers: `n > 0` (includes `n >= 10`, which Pattern 1 doesn't cover)
- Pattern 3 covers: `n < 0`
- Pattern 4 covers: everything else

**Current Implementation:**
The exhaustiveness checker in `src/core/core.gleam` uses Maranget's algorithm but treats all patterns with the same constructor as equivalent, ignoring guards.

**Required Changes:**

#### File: `src/core/core.gleam`

Update the exhaustiveness checking to handle guards (around line 2720):

```gleam
/// Check exhaustiveness of pattern matching.
///
/// Returns a list of missing patterns (witnesses).
/// Empty list means the match is exhaustive.
///
/// KEY FIX: Guard conditions must be considered when determining coverage.
/// A pattern with a guard does NOT subsume the same pattern without the guard.
pub fn check_exhaustiveness(
  s: State,
  cases: List(Case),
  span: Span,
) -> List(Error) {
  // Build the matrix of patterns
  let matrix = build_pattern_matrix(cases)
  
  // Check if matrix is exhaustive
  case is_exhaustive(matrix, PAny) {
    True => []  // Exhaustive - no errors
    False => {
      // Get missing patterns
      let missing = get_missing_patterns(matrix, PAny)
      list.map(missing, fn(pattern) {
        MatchMissingCase(span, pattern)
      })
    }
  }
}

/// Check if a pattern matrix is exhaustive.
///
/// KEY FIX: When comparing patterns, consider guards.
/// Two patterns with the same constructor but different guards
/// are NOT equivalent - both may be needed.
fn is_exhaustive(matrix: Matrix, scrutinee_type: Pattern) -> Bool {
  case matrix {
    [] => False  // Empty matrix is not exhaustive (unless scrutinee is uninhabited)
    
    [row, ..] => {
      // Check if any row has a wildcard or covers all cases
      case row {
        [PAny, ..] => True  // Wildcard covers everything
        [PAs(PAny, _), ..] => True  // As-pattern with wildcard
        [PCtr(tag, _), ..] => {
          // Constructor pattern - check all constructors of this type
          // KEY: Also consider guards
          check_constructor_exhaustive(matrix, tag, scrutinee_type)
        }
        // ... other cases ...
      }
    }
  }
}

/// Check if constructor patterns are exhaustive.
///
/// KEY FIX: Patterns with guards don't subsume patterns without guards.
fn check_constructor_exhaustive(
  matrix: Matrix,
  tag: String,
  scrutinee_type: Pattern,
) -> Bool {
  // Get all constructors of this type
  let all_constructors = get_constructors_for_type(scrutinee_type)
  
  // Check each constructor
  list.all(all_constructors, fn(ctor) {
    // Check if any row matches this constructor
    has_constructor_match(matrix, ctor.tag)
  })
}

/// Check if matrix has a row matching the given constructor.
///
/// KEY FIX: A row with a guard does NOT subsume a row without the guard.
fn has_constructor_match(matrix: Matrix, tag: String) -> Bool {
  list.any(matrix, fn(row) {
    case row {
      [PCtr(row_tag, _), ..] => {
        // Same constructor - but check guards!
        if row_tag == tag {
          // If this row has a guard, it doesn't subsume unguarded patterns
          // We need to check if there's an unguarded pattern or if guards cover all cases
          has_guard(row) || is_unguarded(row)
        } else {
          False
        }
      }
      [PAny, ..] => True  // Wildcard matches
      _ => False
    }
  })
}

/// Check if a row has a guard condition.
fn has_guard(row: Row) -> Bool {
  // Rows with guards have a guard expression
  // This depends on the Row representation
  case row {
    // Pattern with guard
    [#(pattern, Some(_guard)), ..] => True
    _ => False
  }
}

/// Check if a row is unguarded.
fn is_unguarded(row: Row) -> Bool {
  !has_guard(row)
}
```

**Alternative Approach (Simpler):**

If the full Maranget extension is too complex, a simpler fix is:

```gleam
/// Simplified exhaustiveness check that doesn't flag guarded patterns as redundant.
fn is_exhaustive_simple(matrix: Matrix, scrutinee_type: Pattern) -> Bool {
  // If any row has a guard, skip exhaustiveness checking for that row
  // This is conservative but safe
  let has_guards = list.any(matrix, has_guard)
  
  if has_guards {
    // Can't determine exhaustiveness with guards - assume exhaustive
    // (Better to miss a redundancy warning than give a false positive)
    True
  } else {
    // No guards - use standard Maranget algorithm
    is_exhaustive_standard(matrix, scrutinee_type)
  }
}
```

**Testing:**
```bash
gleam run check examples/tao/programs/03-pattern-matching/match_guard.tao
# Should pass type checking (no redundant pattern errors)
```

---

### 3.2 Handle Infinite Loop Evaluation

**Affected Tests:** `loop.tao`

**Problem:** Infinite loops without `break` are evaluated and normalized, producing output like `%fix loop = #True` instead of being recognized as non-terminating.

**Current Behavior:**
```tao
loop {
  True
}
// Desugars to: fix loop -> (True; loop ())
// Evaluates to: %fix loop = #True
```

**Expected Behavior:**
- Infinite loops should either:
  - Time out during evaluation
  - Return Unit (representing non-termination)
  - Be a compile-time warning/error

**Required Changes:**

#### Option A: Runtime Timeout (Recommended)

Add a step counter to the evaluator:

```gleam
/// Evaluation state with step counter.
pub type EvalState {
  EvalState(
    env: Env,
    ffi: FFI,
    steps: Int,
    max_steps: Int,
  )
}

/// Evaluate with step limit.
pub fn eval_with_limit(ffi: FFI, env: Env, term: Term, max_steps: Int) -> Value {
  eval_loop(env, term, EvalState(env, ffi, 0, max_steps))
}

fn eval_loop(env: Env, term: Term, state: EvalState) -> Value {
  // Check step limit
  if state.steps >= state.max_steps {
    // Timeout - return Unit to indicate non-termination
    VUnit
  } else {
    // Continue evaluation
    case term {
      // ... existing cases ...
      
      Fix(name, body, span) => {
        // Unfold fixpoint with incremented step counter
        let new_state = EvalState(..state, steps: state.steps + 1)
        let body_val = eval_loop([VFix(name, env, body), ..env], body, new_state)
        body_val
      }
      
      // ... rest of cases ...
    }
  }
}
```

#### Option B: Static Analysis (Conservative)

Detect obvious infinite loops at compile time:

```gleam
/// Check if a fixpoint has a base case.
fn has_base_case(body: Term) -> Bool {
  // Simple heuristic: check if body contains a conditional
  // that might terminate the recursion
  case body {
    Match(_, _, cases, _) => {
      // Match expression - might have base case
      list.any(cases, fn(c) {
        // Check if any case doesn't recurse
        !contains_fix_ref(c.body)
      })
    }
    If(_, then_branch, else_branch, _) => {
      // Conditional - might have base case
      !contains_fix_ref(then_branch) || !contains_fix_ref(else_branch)
    }
    _ => False  // No obvious base case
  }
}

/// Check if term contains a reference to the fixpoint.
fn contains_fix_ref(term: Term) -> Bool {
  case term {
    Var(index, _) => True  // Might be fixpoint reference
    App(fun, _, arg, _) => contains_fix_ref(fun) || contains_fix_ref(arg)
    // ... recursive cases ...
    _ => False
  }
}
```

**Testing:**
```bash
gleam run run examples/tao/programs/05-control-flow/loop.tao
# Should output: {} (Unit) or timeout gracefully
```

---

## Implementation Order

### Week 1: Quick Wins
1. Add List constructors to prelude (1-2 hours)
2. Implement Test/Run desugaring (2-3 hours)
3. Test and verify fixes

### Week 2: Type Inference
4. Implement Fix type inference (3-4 hours)
5. Test recursive functions and loops
6. Debug any remaining type errors

### Week 3: Advanced Fixes
7. Fix exhaustiveness with guards (4-6 hours)
8. Handle infinite loops (2-3 hours)
9. Final testing and cleanup

---

## Testing Strategy

After each fix, run:
```bash
# Individual test
gleam run check examples/tao/programs/<path>/<test>.tao

# All tests
gleam test

# Check test count
gleam test 2>&1 | grep -E "(passed|failures)"
```

**Success Criteria:**
- All 6 previously failing tests pass
- No new test failures introduced
- Total: 519+ tests passing

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Fix type inference breaks existing code | Medium | High | Run full test suite after each change |
| Exhaustiveness fix is too complex | High | Medium | Use conservative approach (skip guarded patterns) |
| Infinite loop handling affects performance | Low | Low | Make timeout configurable |
| Test/Run changes break test harness | Medium | Medium | Coordinate with test framework changes |

---

## Dependencies

- **Phase 1** (Quick Wins): No dependencies, can be done in parallel
- **Phase 2** (Type Inference): Depends on Phase 1 (control flow tests need prelude)
- **Phase 3** (Advanced): Independent, can be done in parallel with Phase 2

---

## Notes

- The Fix type inference fix is the most critical - it unblocks 3 tests
- The exhaustiveness fix is the most complex - consider the conservative approach first
- The infinite loop fix requires a design decision: timeout vs. static analysis vs. runtime behavior
