# Test Failure Analysis (3 Remaining Failures)

> **Date:** 2026-05-05
> **Status:** 925 tests passing, 3 failures remaining

## Overview

Three tour example tests are failing due to fundamental parser limitations:

1. **t04_04_gadt_expr_test** — Parser doesn't handle `->` return type annotations in match body expressions
2. **t05_10_exhaustiveness_test** — Parser treats `:` in `$match arg : Type` as unexpected token
3. **t07_01_default_values_test** — `$let` with default values + `$match` produces VErr

---

## Failure 1: t04_04_gadt_expr_test

### Tour File Content
```gleam
$let eval = $fn<a: $Type>(expr: #Expr(a)) => $match expr {
| #LitInt(n) => n
| #LitBool(b) => b
| #Add({x, y}) => %i32_add(eval(x), eval(y)) -> $I32
| #IsZero(e) => %i32_eq(eval(x), 0: $I32) -> $Bool({})
}
```

### Actual Result
`VLam` with nested `Err("negation not supported: unexpected operator: >", ...)` and `Err("unexpected token: |", ...)` errors

### Root Cause
The parser's `parse_cases_acc` function parses match body expressions with `parse_term(p5)`. When the body contains `-> $I32`, the parser:
1. Parses `%i32_add(eval(x), eval(y))` as a term (FFI call)
2. Sees `->` which it doesn't recognize as a return type annotation in this context
3. Treats `>` as a comparison operator, causing cascading parse errors
4. The next `|` token is unexpected, causing more errors

### Fix Strategy
**Option A:** Update `parse_cases_acc` to strip `-> ReturnType` from match body expressions (similar to how `$fn` handles it)
**Option B:** Update `parse_term` to optionally consume `-> ReturnType` at the top level

**Recommended: Option A** — Localized fix in `parse_cases_acc`:
After parsing the body term, check if the next tokens are `Op "->"` followed by a type term. If so, consume them and wrap the body in an `Ann(body, type)` or ignore them (since they're just annotations).

---

## Failure 2: t05_10_exhaustiveness_test

### Tour File Content
```gleam
$match #Some(42) : #Option($Int) {
| #Some(x) => x
| #None(_) => 0
}
```

### Actual Result
`VRcd([#("", VErr), #("", VCtr("Some", VNeut(HVar(1), []))), ...])` — Complex error record instead of `VLit(Int(42))`

### Root Cause
The parser's `parse_match` function doesn't handle the `: #Option($Int)` type annotation after the match argument. When parsing `$match #Some(42) : #Option($Int) {`:
1. Parses `$match` keyword
2. Parses `#Some(42)` as the argument
3. Sees `:` which is unexpected — causes parse error
4. The `#Option($Int)` type annotation is left unparsed, causing cascading errors

### Fix Strategy
**Option A:** Update `parse_match` to optionally consume `: Type` after the argument (similar to how `$let` handles type annotations)
**Option B:** Update `parse_term` to optionally consume `: Type` at the end

**Recommended: Option A** — Localized fix in `parse_match`:
After parsing the argument term, check if the next token is `:`. If so, skip `:` and parse the type term (but don't use it — it's just an annotation).

---

## Failure 3: t07_01_default_values_test

### Tour File Content
```gleam
$let point: ${x: $Int, y: $Int = 0} = {x: 1};

$match point {
| {y} => y // field exists and evaluates to 0
}
```

### Actual Result
`VErr`

### Root Cause
This test was already partially fixed (fill_record_defaults added to infer_app), but still produces `VErr`. The issue is likely one of:
1. The `$let` type annotation `${x: $Int, y: $Int = 0}` is not being parsed correctly (the `<` in `$Int` might be interfering)
2. The `fill_record_defaults` function is not being called correctly
3. The `$match` body `| {y} => y` is not being parsed correctly (the `{y}` pattern might be interfering)

### Fix Strategy
**Step 1:** Add unit tests to isolate the issue
**Step 2:** Debug by checking what the parser produces for the type annotation
**Step 3:** Fix the parser or infer logic accordingly

---

## Implementation Plan

### Phase 1: Fix parser to handle `->` in match bodies (t04_04_gadt_expr_test)
1. Read `parse_cases_acc` in `syntax.gleam`
2. After parsing body term, check for `Op "->"` followed by a type term
3. If found, consume them and optionally wrap body in `Ann(body, type)` or ignore
4. Add unit test to verify `parse("$match x { | #LitInt(n) => n -> $I32 }")` produces no errors
5. Run tests to verify t04_04_gadt_expr_test passes

### Phase 2: Fix parser to handle `:` in match argument (t05_10_exhaustiveness_test)
1. Read `parse_match` in `syntax.gleam`
2. After parsing argument term, check for `Op ":"` followed by a type term
3. If found, consume them and ignore (they're just annotations)
4. Add unit test to verify `parse("$match x : #Option($Int) { | #Some(x) => x | #None(_) => 0 }")` produces no errors
5. Run tests to verify t05_10_exhaustiveness_test passes

### Phase 3: Debug and fix t07_01_default_values_test
1. Add unit test to parse `$let point: ${x: $Int, y: $Int = 0} = {x: 1}`
2. Check what the parser produces for the type annotation
3. Check what the infer produces for the let binding
4. Fix the parser or infer logic accordingly
5. Run tests to verify t07_01_default_values_test passes

---

## Expected Outcome
After all three fixes: 928 tests passing, 0 failures.
