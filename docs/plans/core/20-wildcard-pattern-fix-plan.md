# Wildcard Pattern Exhaustiveness Bug - Fix Plan and Retrospective

> **Date**: March 2026
> **Status**: 🐛 Root Cause Identified (Pattern Extraction Logic)
> **Test Status**: 520/522 tests passing (99.6%)
> **Severity**: High - prevents wildcard patterns from working

---

## Executive Summary

**Root Cause**: The `extract_pattern_from_clause_items` function in `src/tao/syntax.gleam` is extracting the wrong `AstValue` from match clause items.

**Debug Evidence**:
```
DEBUG clause items: T(|),A,T(->),A
DEBUG extracted pattern: PLit(0)
```

The clause structure is correct (`Pipe, AstValue, Arrow, AstValue`), but the extracted pattern is `PLit(0)` instead of `PWild`. This suggests the extraction logic is finding an `AstValue` from a different source (possibly prelude or another file).

---

## Comprehensive Fix Plan

### Phase 1: Add Comprehensive Debug Logging (COMPLETED)

**Goal**: Understand exactly what's being extracted and from where.

**Steps**:
1. ✅ Add debug logging to `extract_single_clause_from_list`
2. ✅ Log clause items structure
3. ✅ Log extracted pattern
4. ⏳ Add file path and match expression context to debug output

**Testing**:
- Run wildcard pattern example
- Verify debug output shows correct file path
- Verify debug output shows correct clause structure

**Status**: Partially complete - need to add file path context

---

### Phase 2: Identify Source of Wrong Pattern

**Goal**: Determine where `PLit(0)` is coming from.

**Steps**:
1. Add file path to debug output:
   ```gleam
   io.println("DEBUG file: " <> file <> " clause items: " <> inspect_items_short(items))
   ```

2. Add match expression context:
   ```gleam
   io.println("DEBUG scrutinee: " <> inspect_expr_short(scrutinee))
   ```

3. Check if prelude has match expressions with `PLit(0)` patterns

4. Check if multiple files are being parsed together

**Testing**:
- Run wildcard pattern example
- Verify debug output shows correct file path for each clause
- Identify which file produces `PLit(0)`

**Expected Finding**: The `PLit(0)` is likely from:
- Prelude module pattern matching
- Another example file being parsed
- Compiler internal match expressions

---

### Phase 3: Fix Pattern Extraction Logic

**Goal**: Ensure extraction uses the correct `AstValue` from the clause.

**Hypothesis**: The extraction logic searches through nested structures and finds the wrong `AstValue`.

**Current Code**:
```gleam
fn extract_pattern_from_clause_items(items: List(Value(Expr)), pipe_pos: Int) -> Pattern {
  let pattern_items = list.drop(items, pipe_pos + 1) |> list.take(1)
  case pattern_items {
    [AstValue(expr)] -> pattern_ast_to_pattern(expr)
    [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
    [ListValue([ListValue([AstValue(expr)])])] -> pattern_ast_to_pattern(expr)
    [ListValue(inner_items)] -> {
      find_ast_value_in_list(inner_items) |> pattern_ast_to_pattern  // ❌ This searches too broadly
    }
    _ -> {
      let look_ahead = list.drop(items, pipe_pos + 1) |> list.take(5)
      find_any_pattern(look_ahead)  // ❌ This also searches too broadly
    }
  }
}
```

**Problem**: `find_ast_value_in_list` and `find_any_pattern` search through nested structures and may find `AstValue` from unrelated expressions.

**Fix**: Only extract the FIRST `AstValue` after the Pipe, don't search deeply:

```gleam
fn extract_pattern_from_clause_items(items: List(Value(Expr)), pipe_pos: Int) -> Pattern {
  // Pattern should be the FIRST AstValue after the Pipe
  let after_pipe = list.drop(items, pipe_pos + 1)
  
  // Look for the first AstValue (not nested in other structures)
  find_first_ast_value(after_pipe)
  |> pattern_ast_to_pattern
}

fn find_first_ast_value(items: List(Value(Expr))) -> Expr {
  case items {
    [] -> Var("_", Span("error", 0, 0, 0, 0))
    [AstValue(e), ..] -> e  // ✅ Found it!
    [TokenValue(_), ..rest] -> find_first_ast_value(rest)  // Skip tokens
    [KeywordValue(_), ..rest] -> find_first_ast_value(rest)  // Skip keywords
    [ListValue(_), ..rest] -> find_first_ast_value(rest)  // Skip nested lists
    [_, ..rest] -> find_first_ast_value(rest)  // Skip other values
  }
}
```

**Testing**:
- Unit test: `extract_pattern_from_clause_items` with wildcard pattern
- Unit test: `extract_pattern_from_clause_items` with variable pattern
- Unit test: `extract_pattern_from_clause_items` with literal pattern
- Integration test: Full wildcard pattern example
- Integration test: Full variable pattern example

---

### Phase 4: Add Comprehensive Unit Tests

**Goal**: Prevent regression and catch similar issues early.

**Test File**: `test/tao/pattern_extraction_test.gleam`

**Tests to Add**:

1. **Parsing Tests**:
   - `parse_wildcard_pattern_test()` - Wildcard parses without error
   - `parse_variable_pattern_test()` - Variable parses without error
   - `parse_literal_pattern_test()` - Literal parses without error
   - `parse_constructor_pattern_test()` - Constructor parses without error

2. **Pattern Conversion Tests**:
   - `pattern_ast_to_pattern_wildcard_test()` - `Var("_", _)` → `PWild`
   - `pattern_ast_to_pattern_variable_test()` - `Var("n", _)` → `PVar`
   - `pattern_ast_to_pattern_literal_test()` - `Int(42, _)` → `PLit(42)`

3. **Clause Structure Tests**:
   - `clause_structure_wildcard_test()` - Correct structure for wildcard
   - `clause_structure_variable_test()` - Correct structure for variable
   - `clause_structure_guard_test()` - Correct structure with guard

4. **Extraction Tests**:
   - `extract_pattern_wildcard_test()` - Extracts `PWild` from clause
   - `extract_pattern_variable_test()` - Extracts `PVar` from clause
   - `extract_pattern_literal_test()` - Extracts `PLit` from clause
   - `extract_pattern_nested_test()` - Handles nested structures correctly

5. **Integration Tests**:
   - `full_pipeline_wildcard_test()` - Full parse → extract → desugar → check
   - `full_pipeline_variable_test()` - Full pipeline for variable
   - `exhaustiveness_wildcard_test()` - Wildcard recognized as exhaustive

**Testing Strategy**:
- Run tests after every code change
- Add new test for every bug found
- Maintain 100% test coverage for pattern extraction logic

---

### Phase 5: Verify Fix

**Goal**: Ensure fix works for all pattern types.

**Test Matrix**:

| Pattern Type | Example | Should Work |
|--------------|---------|-------------|
| Wildcard | `| _ -> 100` | ✅ |
| Variable | `| n -> 100` | ✅ |
| Literal | `| 0 -> 100` | ✅ |
| Constructor | `| Some(n) -> 100` | ✅ |
| Record | `| {x, y} -> 100` | ✅ |
| Tuple | `| (a, b) -> 100` | ✅ |
| List | `| [h, ..t] -> 100` | ✅ |
| Or | `| 0 | 1 -> 100` | ✅ |
| As | `| n @ Some(_) -> 100` | ✅ |

**Testing**:
- Run all pattern matching examples
- Run all unit tests
- Verify 522/522 tests passing

---

## Retrospective: How Debugging Could Have Been Easier

### What Went Wrong

1. **Lack of Unit Tests for Pattern Extraction**
   - No tests for `extract_pattern_from_clause_items`
   - No tests for `extract_single_clause_from_list`
   - No tests for `find_ast_value_in_list`
   - Bug could have been caught immediately with proper tests

2. **Insufficient Debug Logging**
   - No file path context in debug output
   - No match expression context
   - Had to add logging retroactively

3. **Complex Grammar Structure**
   - `many(seq([...]))` creates nested `ListValue` structures
   - Hard to predict exact structure without debugging
   - No documentation of expected structure

4. **No Grammar Structure Documentation**
   - No examples of what `Pattern` rule produces
   - No examples of what `OrPattern` rule produces
   - Had to reverse-engineer through debugging

### What Could Have Prevented This

1. **Comprehensive Unit Tests from the Start**
   ```gleam
   // Should have had this from day 1:
   pub fn extract_pattern_wildcard_test() {
     let items = [
       TokenValue(Pipe),
       AstValue(Var("_", span)),
       TokenValue(Arrow),
       AstValue(Int(100, span))
     ]
     let pattern = extract_pattern_from_clause_items(items, 0)
     case pattern {
       PWild(_) -> True |> should.be_true
       _ -> False |> should.be_true
     }
   }
   ```

2. **Grammar Structure Documentation**
   ```gleam
   // Should have documented:
   /// Pattern rule produces: AstValue(Expr)
   /// where Expr is one of:
   /// - Var("_", span) for wildcard
   /// - Var(name, span) for variable
   /// - Int(value, span) for literal
   /// - Ctr(name, args, span) for constructor
   ```

3. **Better Debug Tooling**
   - Built-in grammar structure inspector
   - Built-in AST pretty printer
   - Built-in pattern extraction tracer

4. **Stricter Type Safety**
   - Custom type for clause items instead of `List(Value(Expr))`
   - Type-level guarantee of structure
   - Compile-time error for wrong structure

5. **Incremental Development with Tests**
   - Write test for wildcard pattern FIRST
   - Implement grammar to pass test
   - Implement extraction to pass test
   - Never merge without tests passing

### Lessons Learned

1. **Test Every Function That Transforms Data**
   - Especially functions that extract/convert between representations
   - `extract_*` functions are high-risk
   - `to_*` conversion functions are high-risk

2. **Add Debug Logging Early**
   - Add logging when writing complex parsing logic
   - Include context (file, line, expression)
   - Make logging easy to enable/disable

3. **Document Grammar Structure**
   - Document what each rule produces
   - Include examples of output structure
   - Update documentation when grammar changes

4. **Use Simpler Grammar Structures When Possible**
   - Avoid `many(seq([...]))` when simpler alternatives exist
   - Consider flat structures for easier extraction
   - Trade grammar elegance for debugging simplicity

5. **Test the Full Pipeline Incrementally**
   - Test parsing alone
   - Test extraction alone
   - Test conversion alone
   - Test desugaring alone
   - Test full pipeline last

### Action Items for Future Development

1. [ ] Add unit tests for ALL `extract_*` functions
2. [ ] Add unit tests for ALL `to_*` conversion functions
3. [ ] Document grammar structure for all rules
4. [ ] Add debug logging to all complex parsing functions
5. [ ] Create grammar structure inspector tool
6. [ ] Add integration tests for all pattern types
7. [ ] Create test-driven development checklist
8. [ ] Add code review checklist item: "Are there tests for extraction logic?"

---

## Implementation Status

- [x] Phase 1: Add debug logging (partial)
- [ ] Phase 2: Identify source of wrong pattern
- [ ] Phase 3: Fix pattern extraction logic
- [ ] Phase 4: Add comprehensive unit tests
- [ ] Phase 5: Verify fix for all pattern types

---

## Related Documents

- **[docs/plans/core/18-exhaustiveness-wildcard-bug.md](./18-exhaustiveness-wildcard-bug.md)** - Bug summary
- **[docs/plans/core/19-wildcard-pattern-comprehensive-analysis.md](./19-wildcard-pattern-comprehensive-analysis.md)** - Previous analysis
- **[src/core/core.gleam](../../src/core/core.gleam)** - Core exhaustiveness checking
- **[src/tao/syntax.gleam](../../src/tao/syntax.gleam)** - Grammar and pattern extraction
- **[test/tao/pattern_extraction_test.gleam](../../test/tao/pattern_extraction_test.gleam)** - Unit tests (new)
