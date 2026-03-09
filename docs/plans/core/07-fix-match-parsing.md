# Fix Match Expression Parsing

> **Goal**: Fix match expression parsing to enable exhaustiveness checking
> **Status**: 📋 Planned
> **Priority**: Critical (Phase 1)
> **Date**: March 2025

---

## Problem Statement

Match expressions currently fail to parse with "Parse failed" error, blocking:
- Pattern matching functionality
- Exhaustiveness checking
- Case analysis in core programs

---

## Current Implementation

### Grammar Rules (from `src/core/syntax.gleam`)

```gleam
// Match: match arg with motive returning cases
|> grammar.rule("Match", [
  grammar.alt(
    grammar.seq([
      grammar.keyword_pattern("match"),
      grammar.ref("Expr"),
      grammar.keyword_pattern("with"),
      grammar.ref("Expr"),
      grammar.keyword_pattern("returning"),
      grammar.ref("Cases"),
    ]),
    make_match,
    fn(v, p) { format_value(v, p) },
  ),
])

// Cases: pattern -> body, ...
|> grammar.rule("Cases", [
  // Single case: pattern -> body
  grammar.alt(
    grammar.seq([
      grammar.ref("Pattern"),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
    ]),
    make_single_case,
    fn(_, _) { formatter.text("") },
  ),
  // Multiple cases: pattern -> body, cases...
  grammar.alt(
    grammar.seq([
      grammar.ref("Pattern"),
      grammar.token_pattern("Arrow"),
      grammar.ref("Expr"),
      grammar.token_pattern("Comma"),
      grammar.ref("Cases"),
    ]),
    make_case_cons,
    fn(_, _) { formatter.text("") },
  ),
])

// Pattern: _, x @ pat, Type, 42, $I32, {fields}, #Name(pat)
|> grammar.rule("Pattern", [
  // Wildcard: _
  grammar.alt(grammar.token_pattern("Underscore"), make_pattern_any, fn(_, _) { formatter.text("") }),
  // As-pattern: x @ pat
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Ident"),
      grammar.token_pattern("At"),
      grammar.ref("Pattern"),
    ]),
    make_pattern_as,
    fn(_, _) { formatter.text("") },
  ),
  // Constructor pattern: #Name(pat)
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Hash"),
      grammar.token_pattern("Ident"),
      grammar.token_pattern("LParen"),
      grammar.ref("Pattern"),
      grammar.token_pattern("RParen"),
    ]),
    make_pattern_ctr,
    fn(_, _) { formatter.text("") },
  ),
  // Literal pattern: 42
  grammar.alt(grammar.token_pattern("Number"), make_pattern_lit, fn(_, _) { formatter.text("") }),
])
```

### Constructor Pattern Issue

The `Pattern` rule only supports constructor patterns **with arguments**:
```gleam
#Name(pat)  // Supported
```

But match expressions often need constructors **without arguments**:
```gleam
#True   // Not supported in patterns
#False  // Not supported in patterns
#None   // Not supported in patterns
```

---

## Root Cause Analysis

### Issue 1: Constructor Pattern Without Arguments

**Problem**: Pattern rule doesn't support `#Name` (constructor without args).

**Current Pattern Rule**:
```gleam
// Constructor pattern: #Name(pat)
grammar.alt(
  grammar.seq([
    grammar.token_pattern("Hash"),
    grammar.token_pattern("Ident"),
    grammar.token_pattern("LParen"),
    grammar.ref("Pattern"),
    grammar.token_pattern("RParen"),
  ]),
  make_pattern_ctr,
  fn(_, _) { formatter.text("") },
)
```

**Missing**:
```gleam
// Constructor pattern: #Name
grammar.alt(
  grammar.seq([
    grammar.token_pattern("Hash"),
    grammar.token_pattern("Ident"),
  ]),
  make_pattern_ctr_no_arg,
  fn(_, _) { formatter.text("") },
)
```

### Issue 2: Pattern Rule Order

**Problem**: The `Pattern` rule alternatives may not be in optimal order for parsing.

**Current Order**:
1. Wildcard `_`
2. As-pattern `x @ pat`
3. Constructor `#Name(pat)`
4. Literal `42`

**Issue**: Constructor without args `#Name` is not covered at all.

### Issue 3: Expr vs Pattern Conflict

**Problem**: In match expression `match x with $Type returning #Some(_) -> #True`, the parser may be confused about whether `#Some(_)` is an `Expr` or `Pattern`.

**Analysis**: The `Cases` rule correctly references `Pattern`, but the parser may be trying to parse it as `Expr` first due to grammar rule ordering.

---

## Fix Plan

### Step 1: Add Constructor Pattern Without Arguments

**File**: `src/core/syntax.gleam`

**Change**: Add constructor pattern without args to `Pattern` rule:

```gleam
// Pattern: _, x @ pat, #Name, #Name(pat), 42, $I32, {fields}
|> grammar.rule("Pattern", [
  // Wildcard: _
  grammar.alt(grammar.token_pattern("Underscore"), make_pattern_any, fn(_, _) { formatter.text("") }),
  // As-pattern: x @ pat
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Ident"),
      grammar.token_pattern("At"),
      grammar.ref("Pattern"),
    ]),
    make_pattern_as,
    fn(_, _) { formatter.text("") },
  ),
  // Constructor pattern with args: #Name(pat)
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Hash"),
      grammar.token_pattern("Ident"),
      grammar.token_pattern("LParen"),
      grammar.ref("Pattern"),
      grammar.token_pattern("RParen"),
    ]),
    make_pattern_ctr,
    fn(_, _) { formatter.text("") },
  ),
  // Constructor pattern without args: #Name
  grammar.alt(
    grammar.seq([
      grammar.token_pattern("Hash"),
      grammar.token_pattern("Ident"),
    ]),
    make_pattern_ctr_no_arg,
    fn(_, _) { formatter.text("") },
  ),
  // Literal pattern: 42
  grammar.alt(grammar.token_pattern("Number"), make_pattern_lit, fn(_, _) { formatter.text("") }),
])
```

### Step 2: Add Constructor Pattern Without Args Constructor

**File**: `src/core/syntax.gleam`

**Add**:
```gleam
fn make_pattern_ctr_no_arg(values) -> ParseValue {
  case values {
    [TokenValue(hash_token), TokenValue(name_token)] ->
      AsPattern(NPCtr(name_token.value, NPRcd([], get_span(name_token)), get_span(hash_token)))
    _ -> panic as "Expected constructor pattern without args"
  }
}
```

Wait, that's not quite right. Let me check the `NamedPattern` type...

Actually, for constructor without args, we should use a special "unit" pattern or just the constructor tag. Let me check what makes sense semantically.

Looking at the `NamedPattern` type:
```gleam
pub type NamedPattern {
  NPAny(span: Span)                          // _
  NPAs(pattern: NamedPattern, name: String, span: Span)  // x @ pat
  NPTyp(level: Int, span: Span)              // $Type
  NPLit(value: Literal, span: Span)          // 42
  NPLitT(typ: LiteralType, span: Span)       // $I32
  NPRcd(fields: List(#(String, NamedPattern)), span: Span)  // {x: pat}
  NPCtr(tag: String, arg: NamedPattern, span: Span)  // #Name(pat)
}
```

The `NPCtr` variant requires an `arg`. For constructors without args, we could:
1. Use a "unit" pattern (empty record `{}`)
2. Add a new variant `NPCtrNoArg(tag: String, span: Span)`
3. Use `NPAny` as a placeholder

**Option 2** is cleanest. Let me add it:

```gleam
pub type NamedPattern {
  NPAny(span: Span)
  NPAs(pattern: NamedPattern, name: String, span: Span)
  NPTyp(level: Int, span: Span)
  NPLit(value: Literal, span: Span)
  NPLitT(typ: LiteralType, span: Span)
  NPRcd(fields: List(#(String, NamedPattern)), span: Span)
  NPCtr(tag: String, arg: NamedPattern, span: Span)
  NPCtrNoArg(tag: String, span: Span)  // NEW
}
```

### Step 3: Update Pattern Conversion

**File**: `src/core/syntax.gleam`

**Add**: Handle `NPCtrNoArg` in `named_pattern_to_de_bruijn`:

```gleam
fn named_pattern_to_de_bruijn(pattern: NamedPattern, env: List(String)) -> Pattern {
  case pattern {
    NPAny(span) -> PAny(span)
    NPAs(inner, name, span) -> PAs(named_pattern_to_de_bruijn(inner, env), name, span)
    // ... other cases
    NPCtr(tag, arg, span) -> PCtr(tag, named_pattern_to_de_bruijn(arg, env), span)
    NPCtrNoArg(tag, span) -> PCtrNoArg(tag, span)  // NEW
  }
}
```

### Step 4: Update Pattern Type

**File**: `src/core/core.gleam` (or wherever `Pattern` is defined)

**Add**: `PCtrNoArg` variant:

```gleam
pub type Pattern {
  PAny(Span)
  PAs(Pattern, String, Span)
  PCtr(String, Pattern, Span)
  PCtrNoArg(String, Span)  // NEW
  // ... other variants
}
```

### Step 5: Update Pattern Formatting

**File**: `src/core/syntax.gleam`

**Add**: Format `PCtrNoArg`:

```gleam
fn format_pattern(pattern: Pattern, bindings: List(String)) -> formatter.Doc {
  case pattern {
    PAny(_) -> formatter.text("_")
    PAs(inner, name, _) -> formatter.concat([
      formatter.text(name),
      formatter.text(" @ "),
      format_pattern(inner, bindings),
    ])
    PCtr(tag, arg, _) -> formatter.concat([
      formatter.text("#"),
      formatter.text(tag),
      formatter.text("("),
      format_pattern(arg, bindings),
      formatter.text(")"),
    ])
    PCtrNoArg(tag, _) -> formatter.concat([  // NEW
      formatter.text("#"),
      formatter.text(tag),
    ])
    // ... other cases
  }
}
```

---

## Testing Plan

### Test 1: Constructor Without Args in Pattern

```gleam
// Should parse successfully
match x with $Type returning #True -> 1, #False -> 0
```

### Test 2: Constructor With Args in Pattern

```gleam
// Should parse successfully
match x with $Type returning #Some(y) -> y, #None -> 0
```

### Test 3: Wildcard Pattern

```gleam
// Should parse successfully
match x with $Type returning _ -> #True
```

### Test 4: Multiple Cases

```gleam
// Should parse successfully
match x with $Type returning #Some(a) -> a, #None -> 0, _ -> 1
```

### Test 5: Round-Trip

```gleam
// Parse → format → parse should succeed
let source = "match x with $Type returning #True -> 1, #False -> 0"
let result1 = syntax.parse(source)
let formatted = syntax.format(result1.ast)
let result2 = syntax.parse(formatted)
// result2.errors should be []
```

---

## Files to Modify

| File | Changes |
|------|---------|
| `src/core/core.gleam` | Add `PCtrNoArg` to `Pattern` type |
| `src/core/syntax.gleam` | Add `NPCtrNoArg` to `NamedPattern`, add pattern rule, add constructors, add formatting |
| `test/core/syntax_test.gleam` | Add match expression tests |
| `examples/core/` | Add working match examples |
| `examples/core/errors/exhaustiveness_checks/` | Add exhaustiveness examples |

---

## Acceptance Criteria

- [ ] `match x with $Type returning #True -> 1` parses successfully
- [ ] `match x with $Type returning #Some(y) -> y` parses successfully
- [ ] `match x with $Type returning _ -> #True` parses successfully
- [ ] Multiple cases parse successfully
- [ ] Round-trip tests pass
- [ ] Exhaustiveness checking can be integrated

---

## Estimated Effort

**Time**: 2-4 hours

**Complexity**: Medium

**Risk**: Low (isolated change, well-tested pattern)

---

## Related Documents

- **[06-production-ready.md](./06-production-ready.md)** - Production ready plan
- **[02-syntax.md](./02-syntax.md)** - Syntax specification
- **[../grammar/02-grammar-dsl.md](../grammar/02-grammar-dsl.md)** - Grammar DSL documentation

---

## References

- [Core Syntax](../../src/core/syntax.gleam)
- [Core Types](../../src/core/core.gleam)
- [Pattern Grammar](../../src/core/syntax.gleam) (Pattern rule)
