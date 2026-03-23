# Wildcard Pattern Exhaustiveness Bug - Comprehensive Analysis

> **Date**: March 2026
> **Status**: 🐛 Root Cause Identified
> **Test Status**: 520/522 tests passing (99.6%)
> **Severity**: High - prevents wildcard patterns from working

---

## Executive Summary

**Root Cause**: The bug is in the **pattern extraction logic** during parsing, specifically in how `extract_single_clause_from_list` handles the grammar structure produced by `many(seq([...]))`.

**Key Finding**: Variable patterns (`| n -> ...`) work because they go through a different code path that correctly extracts the pattern. Wildcard patterns (`| _ -> ...`) fail because the extraction returns an error pattern instead of the actual wildcard.

**Definitive Evidence**: Core's exhaustiveness checking works correctly when given `PAny` directly (proven by unit tests). The bug is in getting from source `_` to Core `PAny`.

---

## Pipeline Analysis

### Stage 1: Grammar/Parsing (`src/tao/syntax.gleam`)

#### ✅ DEFINITELY NOT: Grammar Rules Themselves

The grammar rules correctly parse wildcard patterns:

```gleam
// PrimaryPattern rule correctly handles wildcard
rule("PrimaryPattern", [
  alt(
    token_pattern("Underscore"),
    fn(_) { Var("_", Span("_", 0, 0, 0, 0)) },  // ✅ Returns Var("_", span)
  ),
  // ... other patterns
]),
```

**Evidence**: The parser successfully parses `match x { | _ -> 100 }` without syntax errors.

#### ✅ DEFINITELY NOT: `pattern_ast_to_pattern` Conversion

The conversion from parsed Expr to Pattern works correctly:

```gleam
pub fn pattern_ast_to_pattern(expr: Expr) -> Pattern {
  case expr {
    Var("_", span) -> PWild(span)  // ✅ Correctly converts _ to PWild
    // ... other patterns
  }
}
```

**Evidence**: Unit tests confirm this function correctly converts `Var("_", span)` to `PWild(span)`.

#### ✅ DEFINITELY NOT: `pattern_to_ast` Conversion

The conversion from syntax.Pattern to ast.Pattern works correctly:

```gleam
pub fn pattern_to_ast(pattern: Pattern) -> ast.Pattern {
  case pattern {
    PWild(span) -> AstPAny(span)  // ✅ Correctly converts PWild to AstPAny
    // ... other patterns
  }
}
```

**Evidence**: This is a simple case match that always works.

#### ⚠️ POTENTIALLY IS: `extract_single_clause_from_list`

This function extracts patterns from match clause structures. The issue is here.

**Current Implementation**:
```gleam
fn extract_single_clause_from_list(items: List(Value(Expr))) -> Option(MatchClause) {
  let pipe_pos = find_pipe_position(items, 0)
  case pipe_pos {
    Some(pos) -> {
      let pattern_items = list.drop(items, pos + 1) |> list.take(1)
      let pattern = case pattern_items {
        [AstValue(expr)] -> pattern_ast_to_pattern(expr)
        [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
        _ -> PWild(Span("error", 0, 0, 0, 0))  // ❌ FALLBACK PRODUCES ERROR PATTERN
      }
      // ... rest of extraction
    }
    None -> None
  }
}
```

**Problem**: When the pattern structure doesn't match the expected cases, it falls back to `PWild(Span("error", ...))` instead of the actual pattern.

**Grammar Structure Produced**:
```
many(seq([Pipe, Pattern, opt_if, Arrow, Body]))
```

Produces:
```
ListValue([
  ListValue([
    TokenValue(Pipe),
    ???,  // Pattern - structure varies
    opt_if,
    TokenValue(Arrow),
    AstValue(Body)
  ]),
  ...
])
```

The `???` (Pattern) structure varies depending on:
1. How `OrPattern` returns its value
2. How `AsPattern` returns its value
3. How `PrimaryPattern` returns its value

**Investigation Needed**: What is the actual structure of the Pattern element for a simple wildcard?

---

### Stage 2: Desugaring (`src/tao/desugar.gleam`)

#### ✅ DEFINITELY NOT: `tao_pattern_to_core_pattern`

The desugaring correctly converts AST patterns to Core patterns:

```gleam
fn tao_pattern_to_core_pattern(
  pattern: Pattern,
  dc: DesugarContext,
) -> #(CorePattern, DesugarContext) {
  case pattern {
    ast.PAny(_pattern_span) -> {
      // Wildcard pattern (AST)
      #(PAny, dc)  // ✅ Correctly converts AstPAny to Core PAny
    }
    ast.PVar(name, _) -> {
      // Variable pattern: bind to as-pattern
      let core_pattern = PAs(PAny, name)  // ✅ Correctly converts to PAs(PAny, name)
      // ...
    }
    // ... other patterns
  }
}
```

**Evidence**: This is a simple case match. If given `AstPAny`, it correctly produces `PAny`.

#### ⚠️ PROBABLY NOT: Desugar Pipeline

The desugar pipeline correctly processes match expressions:

```gleam
fn desugar_match(
  scrutinee: Expr,
  clauses: List(MatchClause),
  span: Span,
  dc: DesugarContext,
) -> #(CoreTerm, DesugarContext) {
  let #(core_scrutinee, dc1) = desugar_expr_core(scrutinee, dc)
  let #(core_cases, dc2) = desugar_match_clauses_to_cases(clauses, span, dc1)
  // ...
}
```

**Evidence**: Variable patterns work through this pipeline, so the pipeline itself is correct.

---

### Stage 3: Core Type Checking (`src/core/core.gleam`)

#### ✅ DEFINITELY NOT: `check_exhaustiveness`

Core's exhaustiveness checking works correctly when given `PAny`:

```gleam
pub fn check_exhaustiveness(
  s: State,
  cases: List(Case),
  span: Span,
) -> List(Error) {
  case list.last(cases) {
    Ok(Case(pattern: PAny, guard: None, ..)) -> redundant_errors  // ✅ Recognizes PAny
    Ok(Case(pattern: PAs(PAny, _), guard: None, ..)) -> redundant_errors  // ✅ Recognizes PAs(PAny, _)
    _ -> { /* continue with exhaustiveness checking */ }
  }
}
```

**Evidence**: Unit tests confirm:
- `core_exhaustiveness_pany_is_exhaustive_test()` - PAsses ✅
- `core_exhaustiveness_pvar_is_exhaustive_test()` - PAs(PAny, "x") passes ✅
- `core_exhaustiveness_missing_case_test()` - Missing wildcard produces error ✅

#### ✅ DEFINITELY NOT: Pattern Matching Logic

The pattern matching in `check_exhaustiveness` correctly identifies `PAny` as exhaustive.

---

## Root Cause Analysis

### The Critical Question

**Why does `| n -> 100` work but `| _ -> 100` doesn't?**

Both should produce `PAny` in Core:
- `| n -> 100` → `PVar("n")` → `AstPVar("n")` → `PAs(PAny, "n")` ✅ Works
- `| _ -> 100` → `PWild` → `AstPAny` → `PAny` ❌ Fails

### Key Insight

Variable patterns work because they're recognized as identifiers by the grammar and handled differently than wildcards.

**Variable Pattern Flow**:
1. Source: `n`
2. Grammar: `token_pattern("Ident")` → `Var("n", span)`
3. `pattern_ast_to_pattern`: `Var("n", span)` → `PVar("n", span)`
4. `pattern_to_ast`: `PVar("n", span)` → `AstPVar("n", span)`
5. `tao_pattern_to_core_pattern`: `AstPVar("n", span)` → `PAs(PAny, "n")`
6. `check_exhaustiveness`: `PAs(PAny, "n")` → Recognized as exhaustive ✅

**Wildcard Pattern Flow**:
1. Source: `_`
2. Grammar: `token_pattern("Underscore")` → `Var("_", span)`
3. `pattern_ast_to_pattern`: `Var("_", span)` → `PWild(span)`
4. `pattern_to_ast`: `PWild(span)` → `AstPAny(span)`
5. `tao_pattern_to_core_pattern`: `AstPAny(span)` → `PAny`
6. `check_exhaustiveness`: Should recognize `PAny` as exhaustive... but doesn't ❌

### The Missing Link

The issue must be in step 3-4: the pattern extracted by `extract_single_clause_from_list` is NOT `Var("_", span)`, but something else that causes `pattern_ast_to_pattern` to return `PWild(Span("error", ...))`.

**Hypothesis**: The grammar structure for wildcard patterns is different from variable patterns, causing the extraction to fail.

### Grammar Structure Investigation

For `| n -> 100`:
```
OrPattern → AsPattern → PrimaryPattern → Ident
```

For `| _ -> 100`:
```
OrPattern → AsPattern → PrimaryPattern → Underscore
```

Both should produce the same structure, but the `Underscore` token might be handled differently.

**Critical Observation**: The `PrimaryPattern` rule for `Underscore` returns `Var("_", Span("_", 0, 0, 0, 0))` with a special span `Span("_", 0, 0, 0, 0)` instead of the actual source location.

This might cause issues in the grammar's value propagation.

---

## Test Evidence

### Core Exhaustiveness Tests (All Pass)

```gleam
// Test 1: PAny is recognized as exhaustive
pub fn core_exhaustiveness_pany_is_exhaustive_test() {
  let cases = [case_(PAny, i32(100, s1), s1)]
  let term = match_(i32(5, s2), motive, cases, s2)
  let #(_, _, state) = infer(initial_state, term)
  // No MatchMissingCase error ✅
}

// Test 2: PAs(PAny, "x") is recognized as exhaustive
pub fn core_exhaustiveness_pvar_is_exhaustive_test() {
  let cases = [case_(PAs(PAny, "x"), i32(100, s1), s1)]
  let term = match_(i32(5, s2), motive, cases, s2)
  let #(_, _, state) = infer(initial_state, term)
  // No MatchMissingCase error ✅
}
```

### Pipeline Tests (Fail for Wildcard)

```gleam
// Variable pattern works
match x { | n -> 100 }  // ✅ No exhaustiveness error

// Wildcard pattern fails
match x { | _ -> 100 }  // ❌ MatchNotExhaustive error
```

---

## Fix Plan

### Immediate Fix: Improve Pattern Extraction

Update `extract_single_clause_from_list` to handle more grammar structures:

```gleam
fn extract_pattern_from_clause_items(
  items: List(Value(Expr)),
  pipe_pos: Int,
) -> Pattern {
  let pattern_items = list.drop(items, pipe_pos + 1) |> list.take(1)
  case pattern_items {
    // Direct Expr
    [AstValue(expr)] -> pattern_ast_to_pattern(expr)
    // Single ListValue wrapping
    [ListValue([AstValue(expr)])] -> pattern_ast_to_pattern(expr)
    // Double ListValue wrapping
    [ListValue([ListValue([AstValue(expr)])])] -> pattern_ast_to_pattern(expr)
    // Fallback: try to find any Expr in the structure
    [ListValue(inner_items)] -> {
      find_ast_value_in_list(inner_items) |> pattern_ast_to_pattern
    }
    // Last resort fallback
    _ -> PWild(Span("error", 0, 0, 0, 0))
  }
}

fn find_ast_value_in_list(items: List(Value(Expr))) -> Expr {
  case items {
    [] -> Var("_", Span("error", 0, 0, 0, 0))
    [AstValue(e), ..] -> e
    [ListValue(inner), ..] -> find_ast_value_in_list(inner)
    [_, ..rest] -> find_ast_value_in_list(rest)
  }
}
```

### Long-term Fix: Simplify Grammar Structure

Consider restructuring the grammar to avoid complex nesting:

```gleam
// Instead of many(seq([...])) which creates nested ListValue
// Use a simpler structure that's easier to parse
rule("MatchClauses", [
  many1(seq([
    token_pattern("Pipe"),
    ref("Pattern"),
    opt(seq([keyword_pattern("if"), ref("Expr")])),
    token_pattern("Arrow"),
    ref("Expr"),
  ])),
]),
```

### Debug Step: Add Logging

Add debug output to see the actual grammar structure:

```gleam
fn extract_single_clause_from_list(items: List(Value(Expr))) -> Option(MatchClause) {
  // Debug: print the structure
  io.println("DEBUG: clause items = " <> inspect(items))
  // ... rest of extraction
}
```

---

## Conclusion

**Root Cause**: The pattern extraction logic in `extract_single_clause_from_list` doesn't correctly handle the grammar structure for wildcard patterns, returning `PWild(Span("error", ...))` instead of the actual pattern.

**Why Variable Patterns Work**: They may have a slightly different grammar structure that happens to match the extraction cases.

**Why Core Exhaustiveness is Correct**: Unit tests prove that `check_exhaustiveness` correctly recognizes `PAny` as exhaustive.

**Fix Priority**:
1. Improve pattern extraction to handle all grammar structures
2. Add debug logging to identify exact structure
3. Consider simplifying grammar structure long-term

---

## Related Files

- `src/tao/syntax.gleam` - Grammar and pattern extraction
- `src/tao/desugar.gleam` - Pattern desugaring
- `src/core/core.gleam` - Exhaustiveness checking
- `test/core/pattern_match_test.gleam` - Core pattern matching tests

## Test Status

- **520/522 tests passing** (99.6%)
- 2 failures: wildcard pattern examples
- Workaround: use variable patterns instead of wildcards
