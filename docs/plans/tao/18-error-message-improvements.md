# Error Message Improvement Plan

## Executive Summary

The current error messages in the Tao compiler provide basic information but lack the contextual details needed for efficient debugging. This plan outlines improvements to error reporting across parsing, type checking, and evaluation phases.

## Current State Analysis

### Parsing Errors

**Current Format:**
```
Parse error: Parse error: end of input got import
  at input:26:3
```

**Issues:**
- Generic "Parse error" message repeated
- No context about what was expected
- No source snippet showing the error location
- "input" instead of meaningful file name

### Type Errors

**Current Format:**
```
error[E0102]: Undefined variable
  ┌─ tao:3:1
3 │ True
  │ ^^^^
4 │
  = note: Variable at index 0 is not defined in this scope
  = note: Variables must be defined before they are used
  = hint: Check variable name and scope
```

**Issues:**
- Good: Has source snippet and error code
- Missing: What variables ARE in scope
- Missing: Similar variable names (typo detection)
- Generic hints that don't help with specific cases

### Pattern Match Errors

**Current Format:**
```
error[E0202]: Pattern match not exhaustive
  ┌─ tao:5:1
5 │ match x {
  │ ^^^^^^^
  = note: Pattern match is not exhaustive
  = note: Missing case for pattern
  = hint: Add a case for the missing pattern
```

**Issues:**
- Doesn't say WHAT pattern is missing
- Doesn't show the type being matched
- Doesn't show existing patterns for context
- Generic hints

### Hole Errors

**Current Format:**
```
error[E0106]: Unsolved hole
  ┌─ tao:5:1
5 │ match x -> I32 {
  │ ^^^^^^^
  = note: Hole #-999 was not solved during type checking
  = note: Holes are development placeholders
```

**Issues:**
- Hole ID (-999) is not meaningful
- Doesn't say what type was expected
- Doesn't suggest how to fix it

---

## Improvement Plan

### Phase 1: Source Snippet Enhancement (2-3 hours)

**Goal:** Show better context for all error locations.

**Changes:**
1. **Multi-line snippets:** Show 3-5 lines around error, not just the error line
2. **Error highlighting:** Use `^` markers to show exact error span
3. **Line numbers:** Show line numbers for all displayed lines
4. **File path:** Show full file path, not just "tao" or "input"

**Example After:**
```
error[E0102]: Undefined variable
  ┌─ examples/test.tao:3:1
  │
1 │ import prelude/bool
2 │
3 │ True
  │ ──── Variable 'True' is not defined
4 │
  │
  = note: Variable at index 0 is not defined in this scope
  = help: Did you forget to import 'prelude/bool'?
```

**Implementation:**
- Update `source_snippet.gleam` to support multi-line display
- Update `error_reporter.gleam` to include file paths
- Add helper function to show surrounding context

---

### Phase 2: Parsing Error Improvements (3-4 hours)

**Goal:** Make parse errors actionable with specific expectations.

**Changes:**
1. **Expected tokens:** List what tokens were expected at the error location
2. **Common mistakes:** Detect and suggest fixes for common errors
3. **Grammar context:** Show which grammar rule was being parsed

**Example After:**
```
error[E0001]: Parse error
  ┌─ examples/test.tao:1:1
  │
1 │ import prelude/bool
  │ ────── Unexpected 'import'
  │
  = note: Expected one of: function definition, let binding, expression
  = note: 'import' statements are not yet supported in this context
  = help: Import functionality is planned but not yet implemented
  = help: See docs/plans/tao/17-comprehensive-remaining-issues.md
```

**Implementation:**
- Enhance `grammar.gleam` to track expected tokens
- Add error context to `ParseError` type
- Create common mistake detection patterns

---

### Phase 3: Type Error Context (4-6 hours)

**Goal:** Provide scope information and suggestions for type errors.

**Changes:**
1. **In-scope variables:** List available variables in the current scope
2. **Type information:** Show the type of relevant expressions
3. **Typo detection:** Suggest similar variable names
4. **Constructor availability:** Show which constructors are in scope

**Example After:**
```
error[E0102]: Undefined variable
  ┌─ examples/test.tao:5:3
  │
5 │   Some(x) -> x
  │   ──── Constructor 'Some' is not in scope
  │
  = note: Variable at index 0 is not defined in this scope
  = help: 'Some' is a constructor from 'prelude/option'
  = help: Add 'import prelude/option' to bring 'Some' into scope
  = note: Available constructors: True, False, LT, EQ, GT
```

**Implementation:**
- Extend `TypeError` type with scope information
- Add typo detection using Levenshtein distance
- Track constructor availability in type checker state
- Update `core.gleam` error generation to include context

---

### Phase 4: Pattern Match Diagnostics (3-4 hours)

**Goal:** Show exactly what patterns are missing or redundant.

**Changes:**
1. **Missing patterns:** Show the specific missing pattern
2. **Type being matched:** Display the type of the scrutinee
3. **Existing patterns:** List all patterns in the match
4. **Suggested fix:** Show the exact code to add

**Example After:**
```
error[E0202]: Pattern match not exhaustive
  ┌─ examples/test.tao:5:1
  │
5 │ ╭ match x {
6 │ │   | n if n > 0 -> "positive"
7 │ │   | _ -> "non-positive"
8 │ │ }
  │ ╰─^ Missing case for pattern
  │
  = note: Type being matched: I32
  = note: Existing patterns:
            - n if n > 0
            - _ (wildcard with guard)
  = note: Missing pattern: n where n <= 0
  = help: Add case: '| n if n <= 0 -> ...'
  = help: Or use unguarded wildcard: '| _ -> ...'
```

**Implementation:**
- Enhance `check_exhaustiveness` to return detailed witness info
- Format missing patterns as Tao syntax
- Show type information for scrutinee
- Generate suggested fix code

---

### Phase 5: Hole and Unification Errors (2-3 hours)

**Goal:** Make hole errors understandable and actionable.

**Changes:**
1. **Hole location:** Show where the hole was created
2. **Expected type:** Display what type the hole should have
3. **Unification failures:** Show why unification failed
4. **Debug mode:** Optional verbose output for compiler developers

**Example After:**
```
error[E0106]: Unsolved hole
  ┌─ examples/test.tao:5:1
  │
5 │ match x -> I32 {
  │ ───── Type annotation creates hole ?-999
6 │   | y -> y
7 │ }
  │
  = note: Hole #-999 was not solved during type checking
  = note: Expected type: I32
  = note: Actual type: Var(0) (unbound type variable)
  = help: This hole should be solved by unification with clause types
  = help: Check that all match clauses return the same type
  = debug: Hole created at src/tao/desugar.gleam:1406
```

**Implementation:**
- Track hole creation location in desugarer
- Store expected type with hole ID
- Add unification failure context to errors
- Implement debug mode flag for verbose output

---

### Phase 6: Evaluation Errors (2-3 hours)

**Goal:** Provide context for runtime/evaluation errors.

**Changes:**
1. **Call stack:** Show the evaluation context when errors occur
2. **Value display:** Show the actual values involved in errors
3. **Infinite loop detection:** Warn about potential infinite recursion
4. **Step limit:** Configurable evaluation step limit with informative error

**Example After:**
```
error[E0301]: Evaluation step limit exceeded
  ┌─ examples/test.tao:10:1
   │
10 │ factorial(5)
   │ ──────────── Infinite recursion detected?
   │
   = note: Evaluation exceeded 10000 steps
   = note: Call stack:
             factorial(5)
             → factorial(4)
             → factorial(3)
             → factorial(2)
             → factorial(1)
             → factorial(0)
             → factorial(-1)  ← Base case not reached!
   = help: Check that your base case covers all inputs
   = help: Add '| 0 -> 1' case if missing
   = help: Ensure recursive calls converge to base case
```

**Implementation:**
- Add step counter to evaluation state
- Track call stack during evaluation
- Detect repeating states (potential infinite loops)
- Format evaluation context for errors

---

### Phase 7: Developer Debug Mode (2-3 hours)

**Goal:** Enable verbose debugging for compiler development.

**Changes:**
1. **--debug flag:** Enable verbose output for all phases
2. **AST dump:** Show parsed AST structure
3. **Core term dump:** Show desugared Core terms
4. **Type inference trace:** Show unification steps
5. **Evaluation trace:** Step-by-step evaluation (optional)

**Example Output:**
```
$ gleam run check test.tao --debug

=== Parsing ===
Parsed AST:
  Module(
    body: [
      Import(ImportModule("prelude/bool", ...)),
      Match(Var("x", ...), [...])
    ]
  )

=== Desugaring ===
Core term:
  Match(
    arg: Var(0),
    motive: Lam("_", Hole(-999)),
    cases: [
      Case(PAs(PAny, "y"), Var(0), None)
    ]
  )

=== Type Checking ===
Initial state: hole_counter=0, var_counter=0
Inferring match argument: Var(0) ⊢ I32
Checking motive: Lam("_", Hole(-999)) against (x:I32) → Type
  Created hole #-999 for return type
  Unifying ?-999 with I32 ✓
Checking clause body: Var(0) against ?-999
  Hole solved: ?-999 ↦ I32

Final state: 0 errors
```

**Implementation:**
- Add `--debug` flag to CLI
- Create debug output functions for each phase
- Thread debug flag through compilation pipeline
- Format output for readability

---

## Implementation Priority

| Phase | Priority | Effort | Impact |
|-------|----------|--------|--------|
| Phase 1: Source Snippets | High | 2-3h | High |
| Phase 2: Parse Errors | High | 3-4h | High |
| Phase 3: Type Context | Medium | 4-6h | Medium |
| Phase 4: Match Diagnostics | Medium | 3-4h | Medium |
| Phase 5: Hole Errors | Low | 2-3h | Low |
| Phase 6: Evaluation Errors | Low | 2-3h | Low |
| Phase 7: Debug Mode | Medium | 2-3h | High (for devs) |

**Total Effort:** 18-26 hours

---

## Quick Wins (Can be done during bug fixes)

While fixing the remaining issues, implement these low-effort improvements:

1. **Add file paths to all errors** (30 min)
   - Update error reporter to use actual file paths

2. **Show available constructors in scope errors** (1 hour)
   - List constructors when variable not found

3. **Add "import prelude/option" suggestion** (30 min)
   - Detect constructor names and suggest imports

4. **Show missing pattern in exhaustiveness errors** (1 hour)
   - Format witness pattern as Tao syntax

5. **Add hole creation location to debug output** (30 min)
   - Track where holes are created in desugarer

**Total Quick Wins:** 3.5 hours

---

## Success Metrics

After implementation:
- [ ] All errors show source snippets with context
- [ ] Parse errors list expected tokens
- [ ] Type errors show in-scope variables
- [ ] Pattern match errors show missing patterns
- [ ] Hole errors show expected types
- [ ] Debug mode available for development
- [ ] Average time to diagnose compiler errors reduced by 50%

---

## Conclusion

Better error messages will significantly reduce debugging time for both users and compiler developers. The quick wins can be implemented immediately while fixing remaining bugs, while the full plan provides a roadmap for systematic improvement.

**Recommended Approach:**
1. Implement quick wins during bug fixes
2. Complete Phases 1-2 for immediate user benefit
3. Complete Phases 3-4 for better pattern matching diagnostics
4. Complete Phases 5-7 for compiler development support
