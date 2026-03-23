# Wildcard Pattern Exhaustiveness Bug - Comprehensive Analysis

> **Date**: March 2026
> **Status**: 🐛 Root Cause Identified (Pattern Extraction Logic)
> **Test Status**: 520/522 tests passing (99.6%)
> **Severity**: High - prevents wildcard patterns from working

---

## Executive Summary

**Root Cause**: The bug is in the **pattern extraction logic** in `extract_pattern_from_clause_items`. The function is extracting the wrong AstValue from the clause items.

**Key Finding from Debug Logging**:
```
DEBUG clause items: T(|),A,T(->),A
DEBUG extracted pattern: PLit(0)
```

The clause items structure is correct: `Pipe, AstValue(pattern), Arrow, AstValue(body)`
But the extracted pattern is `PLit(0)` instead of `PWild`!

This suggests the extraction logic is finding the wrong AstValue, possibly from a different part of the parsed structure (like the prelude or another file).

---

## Pipeline Analysis

### What's Working ✅

1. **Core exhaustiveness checking** - Correctly recognizes `PAny` as exhaustive (proven by unit tests)
2. **Desugaring** - Correctly converts `AstPAny` → `PAny`
3. **AST conversion** - Correctly converts `PWild` → `AstPAny`
4. **pattern_ast_to_pattern** - Correctly converts `Var("_", span)` → `PWild(span)`
5. **Grammar parsing** - Successfully parses `match x { | _ -> 100 }`

### What's Broken ❌

**`extract_pattern_from_clause_items`** is extracting the wrong pattern.

Debug output shows:
- Clause items: `T(|),A,T(->),A` (Pipe, AstValue, Arrow, AstValue) - CORRECT structure
- Extracted pattern: `PLit(0)` - WRONG! Should be `PWild`

This suggests the extraction is finding an AstValue from a DIFFERENT match expression (possibly from the prelude).

---

## Debug Evidence

The debug logging revealed:
```
DEBUG clause items: T(|),A,T(->),A
DEBUG extracted pattern: PLit(0)
DEBUG clause items: T(|),A,T(->),A
DEBUG extracted pattern: PLit(0)
```

This output appears TWICE, suggesting there are TWO match expressions being parsed. Our test file only has ONE match expression (`match x { | _ -> 100 }`).

The `PLit(0)` pattern suggests the extraction is finding a literal `0` from somewhere else - possibly:
1. The prelude module
2. Another example file being parsed
3. Some internal match expression in the compiler

---

## Fix Plan

### Immediate Fix: Improve Pattern Extraction Debugging

Add more targeted debug logging to identify exactly which file and which match expression is being processed.

### Root Cause Hypothesis

The `extract_pattern_from_clause_items` function might be processing clauses from multiple files, and the wildcard pattern in the user's file is being overshadowed by patterns from the prelude or other files.

### Alternative Approach

Instead of trying to fix the extraction logic, consider:
1. Adding file path information to debug output
2. Checking if the prelude has match expressions that are being processed
3. Verifying that the correct file is being type-checked

---

## Implementation Status

- [x] Added debug logging to identify extraction issue
- [x] Discovered pattern extraction finds wrong AstValue
- [x] Identified that multiple match expressions are being processed
- [ ] Add file path to debug output
- [ ] Identify source of `PLit(0)` pattern
- [ ] Fix extraction to use correct AstValue
- [ ] Verify fix works for all pattern types

---

## Related Documents

- **[docs/plans/core/18-exhaustiveness-wildcard-bug.md](./18-exhaustiveness-wildcard-bug.md)** - Bug summary
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core exhaustiveness checking
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Grammar and pattern extraction
