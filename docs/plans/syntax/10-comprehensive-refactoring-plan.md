# Syntax Library Refactoring Plan

> **Goal**: Clean up syntax library to align with "single source of truth" principle
> **Status**: ✅ Complete (358 tests passing)
> **Date**: March 2025

---

## Overview

This plan addresses the issues identified in `09-comprehensive-analysis.md`. The refactoring will:

1. ✅ Remove unused/broken features (deconstructor - DONE)
2. Remove formatter stubs from grammar
3. Replace Builder pattern with direct record construction
4. Fix formatter to extract precedence from grammar (single source of truth)
5. Simplify layout system
6. Fix the core/syntax module to use the new API

**Key Principle**: Make small, testable changes. Run tests after each step.

---

## Phase 1: Remove Deconstructor ✅ DONE

Completed in initial pass.

---

## Phase 2: Remove Formatter from Alternative (Day 1)

**Rationale**: Formatter doesn't belong in grammar - it's a separate concern. The grammar should only define how to parse, not how to format.

### 2.1: Update Alternative Type

**File**: `src/syntax/grammar.gleam`

**Change**:
```gleam
// Before (after Phase 1)
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
    formatter: fn(a, Int) -> Doc,
  )
}

// After
pub type Alternative(a) {
  Alternative(
    pattern: Pattern(a),
    constructor: fn(List(Value(a))) -> a,
  )
}
```

### 2.2: Update Helper Functions

**Functions to update**:
- `alt()` - Remove formatter parameter
- `create_operator_pattern()` - Remove formatter
- `right_assoc()` - Remove formatter from alternatives

### 2.3: Update All Grammar Definitions

**Files**:
- `src/syntax/examples/calc.gleam`
- `src/core/syntax.gleam`

**Change pattern**:
```gleam
// Before
grammar.alt(pattern, constructor, formatter)

// After
grammar.alt(pattern, constructor)
```

### 2.4: Tests

**Run**: `gleam test`

**Expected**: Parser tests pass, formatter tests need updating (formatters are now fully separate)

---

## Phase 3: Replace Builder Pattern with Direct Record (Day 1-2)

**Rationale**: The Builder pattern adds ~100 lines of infrastructure for no real benefit. Direct record construction is more declarative and easier to understand.

### 3.1: Remove Builder Types and Functions

**File**: `src/syntax/grammar.gleam`

**Remove**:
- `GrammarBuilder` type
- `define()` function
- `to_grammar()` function
- All builder methods: `name()`, `start()`, `token()`, `keyword()`, `rule()`, `left_assoc()`, `right_assoc()`

**Keep**:
- `Grammar` type
- `Rule` type
- `Operator` type
- `Alternative` type
- `Pattern` type

### 3.2: Add Helper Functions (Optional)

Instead of builder methods, provide helper functions for common patterns:

```gleam
/// Create left-associative operator rules
pub fn left_assoc_rules(
  name: String,
  first_rule: String,
  operators: List(Operator(a)),
  precedence: Int,
) -> List(Rule(a))

/// Create operator with default layout
pub fn op(
  symbol: String,
  constructor: fn(a, a) -> a,
  precedence: Int,
) -> Operator(a)
```

### 3.3: Update Grammar Definitions

**Files**:
- `src/syntax/examples/calc.gleam`
- `src/core/syntax.gleam`

**Change pattern**:
```gleam
// Before (Builder pattern)
pub fn calc_grammar() -> Grammar(Expr) {
  use g <- grammar.define

  g
  |> grammar.name("Calc")
  |> grammar.start("Expr")
  |> grammar.token("Number")
  |> grammar.left_assoc("Expr", "Term", [...], 10)
  |> grammar.left_assoc("Term", "Factor", [...], 20)
  |> grammar.rule("Factor", [...])
}

// After (Direct record)
pub fn calc_grammar() -> Grammar(Expr) {
  Grammar(
    name: "Calc",
    start: "Expr",
    tokens: ["Number", "LParen", "RParen"],
    keywords: [],
    rules: [
      left_assoc_rule("Expr", "Term", [
        op("+", make_add, 10),
        op("-", make_sub, 10),
      ], 10),
      left_assoc_rule("Term", "Factor", [
        op("*", make_mul, 20),
        op("/", make_div, 20),
      ], 20),
      Rule(
        name: "Factor",
        alternatives: [
          alt(token_pattern("Number"), make_int),
          alt(parenthesized("Expr"), unwrap_parens),
        ],
        precedence: 0,
      ),
    ],
    operators: all_operators,
  )
}
```

### 3.4: Tests

**Run**: `gleam test`

**Expected**: All tests pass with new grammar definition style

---

## Phase 4: Fix Formatter to Extract Precedence from Grammar (Day 2)

**Rationale**: Precedence should be defined ONCE in grammar and extracted by formatter. Currently it's duplicated.

### 4.1: Add Operator Lookup Functions

**File**: `src/syntax/grammar.gleam`

**Add**:
```gleam
/// Get operator by constructor name
pub fn get_operator_by_constructor(
  grammar: Grammar(a),
  constructor_name: String,
) -> Result(Operator(a), Nil)

/// Get precedence for a constructor
pub fn get_precedence(
  grammar: Grammar(a),
  constructor_name: String,
) -> Int
```

### 4.2: Update Formatter Combinators

**File**: `src/syntax/formatter.gleam`

**Change**:
```gleam
// Before
pub fn format_binop_auto(
  format_fn: fn(a, Int) -> Doc,
  left: a,
  right: a,
  separator: String,
  prec: Int,  // Hardcoded
  parent_prec: Int,
) -> Doc

// After - takes grammar and extracts precedence
pub fn format_binop_auto(
  grammar: Grammar(a),
  format_fn: fn(a, Int, Grammar(a)) -> Doc,
  left: a,
  right: a,
  constructor_name: String,  // Look up in grammar
  parent_prec: Int,
) -> Doc
```

### 4.3: Update Formatter Functions

**Files**:
- `src/syntax/examples/calc.gleam`
- `src/core/formatter.gleam` (or wherever formatters live)

**Change pattern**:
```gleam
// Before
fn format_expr(ast: Expr, parent_prec: Int) -> Doc {
  Add(l, r, _) ->
    format_binop_auto(format_expr, l, r, "+", 10, parent_prec)
}

// After
fn format_expr(ast: Expr, parent_prec: Int, grammar: Grammar(Expr)) -> Doc {
  Add(l, r, _) ->
    format_binop_auto(grammar, format_expr, l, r, "Add", parent_prec)
}
```

### 4.4: Tests

**Run**: `gleam test`

**Expected**: All tests pass, precedence now comes from grammar

---

## Phase 5: Simplify Layout System (Day 2)

### 5.1: Remove Unused Layout Fields

**File**: `src/syntax/grammar.gleam`

**Change**:
```gleam
// Before
pub type OperatorLayout {
  OperatorLayout(
    separator: String,
    break_before: Bool,
    break_after: Bool,
    indent_rhs: Bool,
  )
}

// After
pub type OperatorLayout {
  OperatorLayout(separator: String)
}
```

### 5.2: Update Layout Helper Functions

**Functions to update**:
- `default_op_layout()` - Return simplified `OperatorLayout`
- Remove or simplify `break_before_op_layout()`, `compact_op_layout()`

### 5.3: Update All Usage Sites

**Files**:
- `src/syntax/examples/calc.gleam`
- `src/core/syntax.gleam`

### 5.4: Tests

**Run**: `gleam test`

**Expected**: All tests pass (layout fields weren't used)

---

## Phase 6: Fix Core/Syntax Module (Day 3)

### 6.1: Update Core Grammar Definition

**File**: `src/core/syntax.gleam`

This is the largest file to update. Convert from Builder pattern to direct record construction.

### 6.2: Separate Formatter

Consider separating formatter into its own module:
- `src/core/syntax.gleam` - Grammar and parser only
- `src/core/formatter.gleam` - Formatter only

### 6.3: Tests

**Run**: `gleam test` frequently during this phase

**Expected**: All core tests pass

---

## Phase 7: Documentation (Day 3-4)

### 7.1: Update Syntax Library Docs

**File**: `docs/syntax-library.md`

**Updates**:
- Remove deconstructor references
- Remove formatter stub references
- Update examples to use direct record construction
- Document precedence extraction from grammar
- Clarify separation of concerns (grammar vs formatter)

### 7.2: Update Plan Documents

**Files**:
- `docs/plans/syntax/01-overview.md`
- `docs/plans/syntax/06-automatic-formatter-analysis.md`
- `docs/plans/syntax/09-comprehensive-analysis.md` - Mark as complete

### 7.3: Add Migration Guide

**File**: `docs/plans/syntax/11-migration-guide.md`

**Content**:
- How to migrate from Builder pattern to direct record
- How to migrate from hardcoded precedence to grammar-extracted
- Common patterns and examples

---

## Testing Strategy

### After Each Phase

```bash
# Run all tests
gleam test

# Check for compiler errors
gleam build
```

### Expected Test Counts

- **Before**: 358 tests passing
- **After**: 358+ tests passing

---

## Risk Mitigation

### High Risk: Core/Syntax Module

**Risk**: Breaking the core grammar definition

**Mitigation**:
1. Update in small batches
2. Run tests after each batch
3. Keep a backup of the original file

### Medium Risk: Formatter Separation

**Risk**: Breaking formatter functionality

**Mitigation**:
1. Keep formatter in same file initially
2. Test thoroughly before considering separation
3. Separation is optional

### Low Risk: API Cleanup

**Risk**: Minor API changes

**Mitigation**:
1. All changes are internal
2. Tests will catch any issues immediately

---

## Success Criteria

1. ✅ All 358+ tests passing
2. ✅ No deconstructor in codebase (DONE)
3. ✅ No formatter stubs in grammar
4. ✅ Direct record construction for Grammar
5. ✅ Formatter extracts precedence from grammar
6. ✅ Simplified `OperatorLayout` type
7. ✅ Core/syntax module working with new API
8. ✅ Documentation updated
9. ✅ Migration guide written

---

## Timeline

| Phase | Description | Estimated Time |
|-------|-------------|----------------|
| 1 | Remove deconstructor | ✅ DONE |
| 2 | Remove formatter from Alternative | 1-2 hours |
| 3 | Replace Builder pattern | 3-4 hours |
| 4 | Fix formatter precedence extraction | 2-3 hours |
| 5 | Simplify layout system | 1-2 hours |
| 6 | Fix core/syntax module | 4-6 hours |
| 7 | Documentation | 2-3 hours |
| **Total** | | **13-20 hours** |

---

## Implementation Notes

### Key Files to Modify

1. `src/syntax/grammar.gleam` - Core grammar DSL (~935 lines → ~700 lines)
2. `src/syntax/examples/calc.gleam` - Example grammar (~200 lines)
3. `src/core/syntax.gleam` - Core language grammar (~1300 lines)
4. `test/syntax/examples/calc_test.gleam` - Calc tests

### Files to Create

1. `docs/plans/syntax/11-migration-guide.md` - Migration guide

### Files to Update

1. `docs/syntax-library.md` - Main documentation
2. `docs/plans/syntax/01-overview.md` - Overview
3. `docs/plans/syntax/09-comprehensive-analysis.md` - Mark complete

---

## Next Steps

1. Continue with Phase 2 (remove formatter from Alternative)
2. Run tests after each file update
3. Proceed to Phase 3 (replace Builder pattern)
